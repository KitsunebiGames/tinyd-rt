/**
    Minimal D runtime, based of arsd-webassembly.

*/
module object;
import core.internal.hash;

public import core.internal.array.common;
import mem = core.internal.platform.memory;
import core.stdc.string;
import core.lifetime;

alias size_t = typeof(int.sizeof);
alias ptrdiff_t = typeof(cast(void*) 0 - cast(void*) 0);

alias sizediff_t = ptrdiff_t; // For backwards compatibility only.
alias noreturn = typeof(*null); /// bottom type

alias hash_t = size_t; // For backwards compatibility only.
alias equals_t = bool; // For backwards compatibility only.

alias string = immutable(char)[];
alias wstring = immutable(wchar)[];
alias dstring = immutable(dchar)[];

alias _d_newclassT(T) = core.lifetime._d_newclassT!T;

// bare basics class support {
extern(C) bool _xopEquals(const void*, const void*) { return false; } // assert(0);

extern(C) bool __equals(T1, T2)(scope const T1[] lhs, scope const T2[] rhs) {
    if (lhs.length != rhs.length) {
        return false;
    }
    foreach(i; 0..lhs.length) {
        if (lhs[i] != rhs[i]) {
            return false;
        }
    }
    return true;
}

extern (C) Object _d_allocclass(TypeInfo_Class ti) {
    auto ptr = mem.malloc(ti.m_init.length);
    ptr[] = ti.m_init[];
    return cast(Object) ptr.ptr;
}

extern (C) void* _d_dynamic_cast(Object o, TypeInfo_Class c) {
    void* res = null;
    size_t offset = 0;
    if (o && _d_isbaseof2(typeid(o), c, offset)) {
        res = cast(void*) o + offset;
    }
    return res;
}

/*************************************
 * Attempts to cast Object o to class c.
 * Returns o if successful, null if not.
 */
extern (C) void* _d_interface_cast(void* p, TypeInfo_Class c) {
    if (!p)
        return null;

    Interface* pi = **cast(Interface***) p;
    return _d_dynamic_cast(cast(Object)(p - pi.offset), c);
}

extern (C)
int _d_isbaseof2(scope TypeInfo_Class oc, scope const TypeInfo_Class c, scope ref size_t offset) @safe {
    if (oc is c)
        return true;

    do {
        if (oc.base is c)
            return true;

        // Bugzilla 2013: Use depth-first search to calculate offset
        // from the derived (oc) to the base (c).
        foreach (iface; oc.interfaces) {
            if (iface.classinfo is c || _d_isbaseof2(iface.classinfo, c, offset)) {
                offset += iface.offset;
                return true;
            }
        }

        oc = oc.base;
    }
    while (oc);

    return false;
}

int __cmp(T)(scope const T[] lhs, scope const T[] rhs) @trusted pure @nogc nothrow
        if (__traits(isScalar, T)) {
    // Compute U as the implementation type for T
    static if (is(T == ubyte) || is(T == void) || is(T == bool))
        alias U = char;
    else static if (is(T == wchar))
        alias U = ushort;
    else static if (is(T == dchar))
        alias U = uint;
    else static if (is(T == ifloat))
        alias U = float;
    else static if (is(T == idouble))
        alias U = double;
    else static if (is(T == ireal))
        alias U = real;
    else
        alias U = T;

    static if (is(U == char)) {
        int dstrcmp(scope const char[] s1, scope const char[] s2) @trusted pure @nogc nothrow {
            immutable len = s1.length <= s2.length ? s1.length : s2.length;
            if (__ctfe) {
                foreach (const u; 0 .. len) {
                    if (s1[u] != s2[u])
                        return s1[u] > s2[u] ? 1 : -1;
                }
            } else {
                const ret = memcmp(s1.ptr, s2.ptr, len);
                if (ret)
                    return ret;
            }
            return (s1.length > s2.length) - (s1.length < s2.length);
        }

        return dstrcmp(cast(char[]) lhs, cast(char[]) rhs);
    } else static if (!is(U == T)) {
        // Reuse another implementation
        return __cmp(cast(U[]) lhs, cast(U[]) rhs);
    } else {
        version (BigEndian)
            static if (__traits(isUnsigned, T) ? !is(T == __vector) :  is(T : P*, P)) {
                if (!__ctfe) {
                    import core.stdc.string : memcmp;

                    int c = memcmp(lhs.ptr, rhs.ptr, (lhs.length <= rhs.length ? lhs.length
                            : rhs.length) * T.sizeof);
                    if (c)
                        return c;
                    static if (size_t.sizeof <= uint.sizeof && T.sizeof >= 2)
                        return cast(int) lhs.length - cast(int) rhs.length;
                    else
                        return int(lhs.length > rhs.length) - int(lhs.length < rhs.length);
                }
            }

        immutable len = lhs.length <= rhs.length ? lhs.length : rhs.length;
        foreach (const u; 0 .. len) {
            auto a = lhs.ptr[u], b = rhs.ptr[u];
            static if (is(T : creal)) {
                // Use rt.cmath2._Ccmp instead ?
                // Also: if NaN is present, numbers will appear equal.
                auto r = (a.re > b.re) - (a.re < b.re);
                if (!r)
                    r = (a.im > b.im) - (a.im < b.im);
            } else {
                // This pattern for three-way comparison is better than conditional operators
                // See e.g. https://godbolt.org/z/3j4vh1
                const r = (a > b) - (a < b);
            }
            if (r)
                return r;
        }
        return (lhs.length > rhs.length) - (lhs.length < rhs.length);
    }
}

// This function is called by the compiler when dealing with array
// comparisons in the semantic analysis phase of CmpExp. The ordering
// comparison is lowered to a call to this template.
int __cmp(T1, T2)(T1[] s1, T2[] s2)
        if (!__traits(isScalar, T1) && !__traits(isScalar, T2)) {
    import core.internal.traits : Unqual;

    alias U1 = Unqual!T1;
    alias U2 = Unqual!T2;

    static if (is(U1 == void) && is(U2 == void))
        static @trusted ref inout(ubyte) at(inout(void)[] r, size_t i) {
            return (cast(inout(ubyte)*) r.ptr)[i];
        }
    else
        static @trusted ref R at(R)(R[] r, size_t i) {
            return r.ptr[i];
        }

    // All unsigned byte-wide types = > dstrcmp
    immutable len = s1.length <= s2.length ? s1.length : s2.length;

    foreach (const u; 0 .. len) {
        static if (__traits(compiles, __cmp(at(s1, u), at(s2, u)))) {
            auto c = __cmp(at(s1, u), at(s2, u));
            if (c != 0)
                return c;
        } else static if (__traits(compiles, at(s1, u).opCmp(at(s2, u)))) {
            auto c = at(s1, u).opCmp(at(s2, u));
            if (c != 0)
                return c;
        } else static if (__traits(compiles, at(s1, u) < at(s2, u))) {
            if (int result = (at(s1, u) > at(s2, u)) - (at(s1, u) < at(s2, u)))
                return result;
        } else {
            // TODO: fix this legacy bad behavior, see
            // https://issues.dlang.org/show_bug.cgi?id=17244
            static assert(is(U1 == U2), "Internal error.");
            import core.stdc.string : memcmp;

            auto c = (() @trusted => memcmp(&at(s1, u), &at(s2, u), U1.sizeof))();
            if (c != 0)
                return c;
        }
    }
    return (s1.length > s2.length) - (s1.length < s2.length);
}

/**
Support for switch statements switching on strings.
Params:
    caseLabels = sorted array of strings generated by compiler. Note the
        strings are sorted by length first, and then lexicographically.
    condition = string to look up in table
Returns:
    index of match in caseLabels, a negative integer if not found
*/
int __switch(T, caseLabels...)( /*in*/ const scope T[] condition) pure nothrow @safe @nogc {
    // This closes recursion for other cases.
    static if (caseLabels.length == 0) {
        return int.min;
    } else static if (caseLabels.length == 1) {
        return __cmp(condition, caseLabels[0]) == 0 ? 0 : int.min;
    } // To be adjusted after measurements
    // Compile-time inlined binary search.
    else static if (caseLabels.length < 7) {
        int r = void;
        enum mid = cast(int) caseLabels.length / 2;
        if (condition.length == caseLabels[mid].length) {
            r = __cmp(condition, caseLabels[mid]);
            if (r == 0)
                return mid;
        } else {
            // Equivalent to (but faster than) condition.length > caseLabels[$ / 2].length ? 1 : -1
            r = ((condition.length > caseLabels[mid].length) << 1) - 1;
        }

        if (r < 0) {
            // Search the left side
            return __switch!(T, caseLabels[0 .. mid])(condition);
        } else {
            // Search the right side
            return __switch!(T, caseLabels[mid + 1 .. $])(condition) + mid + 1;
        }
    } else {
        // Need immutable array to be accessible in pure code, but case labels are
        // currently coerced to the switch condition type (e.g. const(char)[]).
        pure @trusted nothrow @nogc asImmutable(scope const(T[])[] items) {
            assert(__ctfe); // only @safe for CTFE
            immutable T[][caseLabels.length] result = cast(immutable)(items[]);
            return result;
        }

        static immutable T[][caseLabels.length] cases = asImmutable([caseLabels]);

        // Run-time binary search in a static array of labels.
        return __switchSearch!T(cases[], condition);
    }
}

// binary search in sorted string cases, also see `__switch`.
private int __switchSearch(T)( /*in*/ const scope T[][] cases, /*in*/ const scope T[] condition) pure nothrow @safe @nogc {
    size_t low = 0;
    size_t high = cases.length;

    do {
        auto mid = (low + high) / 2;
        int r = void;
        if (condition.length == cases[mid].length) {
            r = __cmp(condition, cases[mid]);
            if (r == 0)
                return cast(int) mid;
        } else {
            // Generates better code than "expr ? 1 : -1" on dmd and gdc, same with ldc
            r = ((condition.length > cases[mid].length) << 1) - 1;
        }

        if (r > 0)
            low = mid + 1;
        else
            high = mid;
    }
    while (low < high);

    // Not found
    return -1;
}

void __switch_error()(string file = __FILE__, size_t line = __LINE__) {
    import core.stdc.stdlib;
    abort();
}

//TODO: Support someday?
extern (C) void _d_throw_exception(Throwable o) {
    assert(false, "Exception throw: " ~ o.file ~ " (" ~ o.message ~ ")");
}

// for closures
extern (C) void* _d_allocmemory(size_t sz) {
    return mem.malloc(sz).ptr;
}

///For POD structures
extern (C) void* _d_allocmemoryT(TypeInfo ti) {
    return mem.malloc(ti.size).ptr;
}

class Object {
    /// Convert Object to human readable string
    string toString() {
        return "Object";
    }

    /// Compute hash function for Object
    size_t toHash() @trusted nothrow {
        auto addr = cast(size_t) cast(void*) this;
        return addr ^ (addr >>> 4);
    }

    /// Compare against another object. NOT IMPLEMENTED!
    int opCmp(Object o) const {
        assert(false, "not implemented");
    }

    /// Check equivalence againt another object
    bool opEquals(Object o) const {
        return this is o;
    }
}

/// Compare to objects
bool opEquals(Object lhs, Object rhs) {
    // If aliased to the same object or both null => equal
    if (lhs is rhs)
        return true;

    // If either is null => non-equal
    if (lhs is null || rhs is null)
        return false;

    if (!lhs.opEquals(rhs))
        return false;

    // If same exact type => one call to method opEquals
    if (typeid(lhs) is typeid(rhs) ||
        !__ctfe && typeid(lhs).opEquals(typeid(rhs))) /* CTFE doesn't like typeid much. 'is' works, but opEquals doesn't
            (issue 7147). But CTFE also guarantees that equal TypeInfos are
            always identical. So, no opEquals needed during CTFE. */ {
        return true;
    }

    // General case => symmetric calls to method opEquals
    return rhs.opEquals(lhs);
}
/************************
* Returns true if lhs and rhs are equal.
*/
bool opEquals(const Object lhs, const Object rhs) {
    // A hack for the moment.
    return opEquals(cast() lhs, cast() rhs);
}


void destroy(bool initialize = true, T)(ref T obj) if (is(T == struct)) {
    import core.internal.destruction : destructRecurse;

    destructRecurse(obj);

    static if (initialize) {
        import core.internal.lifetime : emplaceInitializer;

        emplaceInitializer(obj); // emplace T.init
    }
}

void destroy(bool initialize = true, T)(T obj) if (is(T == interface)) {
    static assert(__traits(getLinkage, T) == "D", "Invalid call to destroy() on extern(" ~ __traits(getLinkage, T) ~ ") interface");

    destroy!initialize(cast(Object) obj);
}

void destroy(bool initialize = true, T)(ref T obj)
        if (!is(T == struct) && !is(T == interface) && !is(T == class) && !__traits(
            isStaticArray, T)) {
    static if (initialize)
        obj = T.init;
}

void destroy(bool initialize = true, T)(T obj) if (is(T == class)) {
    static if (__traits(getLinkage, T) == "C++") {
        static if (__traits(hasMember, T, "__xdtor"))
            obj.__xdtor();

        static if (initialize) {
            const initializer = __traits(initSymbol, T);
            (cast(void*) obj)[0 .. initializer.length] = initializer[];
        }
    } else {
        // Bypass overloaded opCast
        auto ptr = (() @trusted => *cast(void**)&obj)();
        rt_finalize2(ptr, true, initialize);
    }
}

private extern (D) nothrow alias void function(Object) fp_t;
private extern (C) void rt_finalize2(void* p, bool det = true, bool resetMemory = true) nothrow {
    auto ppv = cast(void**) p;
    if (!p || !*ppv)
        return;

    auto pc = cast(TypeInfo_Class*)*ppv;
    if (det) {
        auto c = *pc;
        do {
            if (c.destructor)
                (cast(fp_t) c.destructor)(cast(Object) p); // call destructor
        }
        while ((c = c.base) !is null);
    }

    if (resetMemory) {
        auto w = (*pc).initializer;
        p[0 .. w.length] = w[];
    }
    *ppv = null; // zero vptr even if `resetMemory` is false
}

extern (C) void _d_callfinalizer(void* p) {
    rt_finalize2(p);
}

private size_t structTypeInfoSize(const TypeInfo ti) pure nothrow @nogc {
    if (ti && typeid(ti) is typeid(TypeInfo_Struct)) {
        auto sti = cast(TypeInfo_Struct) cast(void*) ti;
        if (sti.xdtor)
            return size_t.sizeof;
    }
    return 0;
}

extern (C) void* _d_newitemU(scope const TypeInfo _ti) {
    auto ti = cast() _ti;
    immutable tiSize = structTypeInfoSize(ti);
    immutable itemSize = ti.size;
    immutable size = itemSize + tiSize;
    auto p = mem.malloc(size);

    return p.ptr;
}

static if(__VERSION__ >= 2105)
{
    T* _d_newitemT(T)() @trusted {
        TypeInfo _ti = typeid(T);
        auto p = _d_newitemU(_ti);
        memset(p, 0, _ti.size);
        return cast(T*) p;
    }
}
else static if(__VERSION__ < 2105)
{
    extern(C) void* _d_newitemT(in TypeInfo _ti) {
        auto p = _d_newitemU(_ti);
        memset(p, 0, _ti.size);
        return cast(void*) p;
    }
}

alias AliasSeq(T...) = T;
static foreach (type; AliasSeq!(bool, byte, char, dchar, double, float, int, long, short, ubyte, uint, ulong, ushort, void, wchar)) {
    mixin(q{
		class TypeInfo_}
            ~ type.mangleof ~ q{ : TypeInfo {
            override string toString() const pure nothrow @safe { return type.stringof; }
			override size_t size() const { return type.sizeof; }
            override @property size_t talign() const pure nothrow
            {
                return type.alignof;
            }

			override bool equals(in void* a, in void* b) const {
				static if(is(type == void))
					return false;
				else
				return (*(cast(type*) a) == (*(cast(type*) b)));
			}
            static if(!is(type == void))
            override size_t getHash(scope const void* p) @trusted const nothrow
            {
                return hashOf(*cast(const type *)p);
            }
			override const(void)[] initializer() pure nothrow @trusted const
			{
				static if(__traits(isZeroInit, type))
					return (cast(void*)null)[0 .. type.sizeof];
				else
				{
					static immutable type[1] c;
					return c;
				}
			}
		}
		class TypeInfo_A}
            ~ type.mangleof ~ q{ : TypeInfo_Array {
            override string toString() const { return (type[]).stringof; }
			override @property const(TypeInfo) next() const { return cast(inout)typeid(type); }
            override size_t getHash(scope const void* p) @trusted const nothrow
            {
                return hashOf(*cast(const type[]*) p);
            }

			override bool equals(in void* av, in void* bv) const {
				type[] a = *(cast(type[]*) av);
				type[] b = *(cast(type[]*) bv);

				static if(is(type == void))
					return false;
				else {
					foreach(idx, item; a)
						if(item != b[idx])
							return false;
					return true;
				}
			}
		}
	});
}

struct Interface {
    TypeInfo_Class classinfo;
    void*[] vtbl;
    size_t offset;
}

///For some reason, getHash for interfaces wanted that
pragma(mangle, "_D9invariant12_d_invariantFC6ObjectZv")
extern (D) void _d_invariant(Object o) {
    TypeInfo_Class c;

    //printf("__d_invariant(%p)\n", o);

    // BUG: needs to be filename/line of caller, not library routine
    assert(o !is null); // just do null check, not invariant check

    c = typeid(o);
    do {
        if (c.classInvariant) {
            (*c.classInvariant)(o);
        }
        c = c.base;
    }
    while (c);
}

extern (C) bool _xopCmp(const void*, const void*) {
    return false;
}

// }

extern (C) int _adEq2(void[] a1, void[] a2, TypeInfo ti) {
    debug (adi)
        printf("_adEq2(a1.length = %d, a2.length = %d)\n", a1.length, a2.length);
    if (a1.length != a2.length)
        return 0; // not equal
    if (!ti.equals(&a1, &a2))
        return 0;
    return 1;
}

class Error {
    this(string msg) {
    }
}

class Throwable : Object {
    interface TraceInfo {
        int opApply(scope int delegate(ref const(char[]))) const;
        int opApply(scope int delegate(ref size_t, ref const(char[]))) const;
        string toString() const;
    }

    alias TraceDeallocator = void function(TraceInfo) nothrow;

    string msg; /// A message describing the error.

    /**
     * The _file name of the D source code corresponding with
     * where the error was thrown from.
     */
    string file;
    /**
     * The _line number of the D source code corresponding with
     * where the error was thrown from.
     */
    size_t line;

    /**
     * The stack trace of where the error happened. This is an opaque object
     * that can either be converted to $(D string), or iterated over with $(D
     * foreach) to extract the items in the stack trace (as strings).
     */
    TraceInfo info;

    /**
     * A reference to the _next error in the list. This is used when a new
     * $(D Throwable) is thrown from inside a $(D catch) block. The originally
     * caught $(D Exception) will be chained to the new $(D Throwable) via this
     * field.
     */
    private Throwable nextInChain;

    private uint _refcount; // 0 : allocated by GC
    // 1 : allocated by _d_newThrowable()
    // 2.. : reference count + 1

    /**
     * Returns:
     * A reference to the _next error in the list. This is used when a new
     * $(D Throwable) is thrown from inside a $(D catch) block. The originally
     * caught $(D Exception) will be chained to the new $(D Throwable) via this
     * field.
     */
    @property inout(Throwable) next() @safe inout return scope pure nothrow @nogc {
        return nextInChain;
    }

    /**
     * Replace next in chain with `tail`.
     * Use `chainTogether` instead if at all possible.
     */
    @property void next(Throwable tail) @safe scope pure nothrow @nogc {
    }

    /**
     * Returns:
     *  mutable reference to the reference count, which is
     *  0 - allocated by the GC, 1 - allocated by _d_newThrowable(),
     *  and >=2 which is the reference count + 1
     * Note:
     *  Marked as `@system` to discourage casual use of it.
     */
    @system @nogc final pure nothrow ref uint refcount() return {
        return _refcount;
    }

    /**
     * Loop over the chain of Throwables.
     */
    int opApply(scope int delegate(Throwable) dg) {
        int result = 0;
        for (Throwable t = this; t; t = t.nextInChain) {
            result = dg(t);
            if (result)
                break;
        }
        return result;
    }

    /**
     * Append `e2` to chain of exceptions that starts with `e1`.
     * Params:
     *  e1 = start of chain (can be null)
     *  e2 = second part of chain (can be null)
     * Returns:
     *  Throwable that is at the start of the chain; null if both `e1` and `e2` are null
     */
    static @system @nogc pure nothrow Throwable chainTogether(return scope Throwable e1, return scope Throwable e2) {
        if (!e1)
            return e2;
        if (!e2)
            return e1;
        if (e2.refcount())
            ++e2.refcount();

        for (auto e = e1; 1; e = e.nextInChain) {
            if (!e.nextInChain) {
                e.nextInChain = e2;
                break;
            }
        }
        return e1;
    }

    @nogc @safe pure nothrow this(string msg, Throwable nextInChain = null) {
        this.msg = msg;
        this.nextInChain = nextInChain;
        if (nextInChain && nextInChain._refcount)
            ++nextInChain._refcount;
        //this.info = _d_traceContext();
    }

    @nogc @safe pure nothrow this(string msg, string file, size_t line, Throwable nextInChain = null) {
        this(msg, nextInChain);
        this.file = file;
        this.line = line;
        //this.info = _d_traceContext();
    }

    @trusted nothrow ~this() {
    }

    /**
     * Overrides $(D Object.toString) and returns the error message.
     * Internally this forwards to the $(D toString) overload that
     * takes a $(D_PARAM sink) delegate.
     */
    override string toString() {
        string s;
        toString((in buf) { s ~= buf; });
        return s;
    }

    /**
     * The Throwable hierarchy uses a toString overload that takes a
     * $(D_PARAM _sink) delegate to avoid GC allocations, which cannot be
     * performed in certain error situations.  Override this $(D
     * toString) method to customize the error message.
     */
    void toString(scope void delegate(in char[]) sink) const {
    }

    /**
     * Get the message describing the error.
     * Base behavior is to return the `Throwable.msg` field.
     * Override to return some other error message.
     *
     * Returns:
     *  Error message
     */
    const(char)[] message() const {
        return this.msg;
    }
}

class Exception : Throwable {

    /**
     * Creates a new instance of Exception. The nextInChain parameter is used
     * internally and should always be $(D null) when passed by user code.
     * This constructor does not automatically throw the newly-created
     * Exception; the $(D throw) statement should be used for that purpose.
     */
    @nogc @safe pure nothrow this(string msg, string file = __FILE__, size_t line = __LINE__, Throwable nextInChain = null) {
        super(msg, file, line, nextInChain);
    }

    @nogc @safe pure nothrow this(string msg, Throwable nextInChain, string file = __FILE__, size_t line = __LINE__) {
        super(msg, file, line, nextInChain);
    }
}


class TypeInfo {
    override string toString() const @safe nothrow {
        return typeid(this).name;
    }

    const(TypeInfo) next() nothrow pure inout @nogc {
        return null;
    }

    size_t size() nothrow pure const @safe @nogc {
        return 0;
    }

    bool equals(in void* p1, in void* p2) const {
        return p1 == p2;
    }

    override size_t toHash() @trusted const nothrow {
        return hashOf(this.toString());
    }

    size_t getHash(scope const void* p) @trusted nothrow const {
        return hashOf(p);
    }

    /**
	* Return default initializer.  If the type should be initialized to all
	* zeros, an array with a null ptr and a length equal to the type size will
	* be returned. For static arrays, this returns the default initializer for
	* a single element of the array, use `tsize` to get the correct size.
	*/
    const(void)[] initializer() const @trusted nothrow pure {
        return (cast(const(void)*) null)[0 .. typeof(null).sizeof];
    }

    const(OffsetTypeInfo)[] offTi() const {
        return null;
    }

    @property uint flags() nothrow pure const @safe @nogc {
        return 0;
    }
    /// Run the destructor on the object and all its sub-objects
    void destroy(void* p) const {
    }
    /// Run the postblit on the object and all its sub-objects
    void postblit(void* p) const {
    }

    @property size_t talign() nothrow pure const {
        return size;
    }
}

class TypeInfo_Class : TypeInfo {
    ubyte[]      m_init;        /** class static initializer
                                    * (init.length gives size in bytes of class)
                                    */
    string      name;           /// class name
    void*[]     vtbl;           /// virtual function pointer table
    Interface[] interfaces;     /// interfaces this class implements
    TypeInfo_Class   base;      /// base class
    void*       destructor;
    void function(Object) classInvariant;
    enum ClassFlags : ushort
    {
        isCOMclass = 0x1,
        noPointers = 0x2,
        hasOffTi = 0x4,
        hasCtor = 0x8,
        hasGetMembers = 0x10,
        hasTypeInfo = 0x20,
        isAbstract = 0x40,
        isCPPclass = 0x80,
        hasDtor = 0x100,
        hasNameSig = 0x200,
    }
    ClassFlags m_flags;
    ushort     depth;           /// inheritance distance from Object
    void*      deallocator;
    OffsetTypeInfo[] m_offTi;
    void function(Object) defaultConstructor;   // default Constructor
    immutable(void)* m_RTInfo;        // data for precise GC
    uint[4] nameSig;            /// unique signature for `name`

    override @property size_t size() nothrow pure const {
        return Object.sizeof;
    }

    override string toString() const pure {
        return name;
    }

    override @property const(OffsetTypeInfo)[] offTi() nothrow pure const {
        return m_offTi;
    }

    override size_t getHash(scope const void* p) @trusted const {
        auto o = *cast(Object*) p;
        return o ? o.toHash() : 0;
    }

    override bool equals(in void* p1, in void* p2) const {
        Object o1 = *cast(Object*) p1;
        Object o2 = *cast(Object*) p2;

        return (o1 is o2) || (o1 && o1.opEquals(o2));
    }

    override const(void)[] initializer() nothrow pure const @safe {
        return m_init;
    }
}

alias ClassInfo = TypeInfo_Class;

// NOT SUPPORTED
class TypeInfo_AssociativeArray : TypeInfo { }

class TypeInfo_Pointer : TypeInfo {
    TypeInfo m_next;

    override bool equals(in void* p1, in void* p2) const {
        return *cast(void**) p1 == *cast(void**) p2;
    }

    override size_t getHash(scope const void* p) @trusted const {
        size_t addr = cast(size_t)*cast(const void**) p;
        return addr ^ (addr >> 4);
    }

    override @property size_t size() nothrow pure const {
        return (void*).sizeof;
    }

    override const(void)[] initializer() const @trusted {
        return (cast(void*) null)[0 .. (void*).sizeof];
    }

    override const(TypeInfo) next() const {
        return m_next;
    }
}

class TypeInfo_Array : TypeInfo {
    TypeInfo value;
    override string toString() const {
        return value.toString() ~ "[]";
    }

    override size_t size() const {
        return (void[]).sizeof;
    }

    override const(TypeInfo) next() const {
        return value;
    }

    override bool equals(in void* p1, in void* p2) const {
        void[] a1 = *cast(void[]*) p1;
        void[] a2 = *cast(void[]*) p2;
        if (a1.length != a2.length)
            return false;
        size_t sz = value.size;
        for (size_t i = 0; i < a1.length; i++) {
            if (!value.equals(a1.ptr + i * sz, a2.ptr + i * sz))
                return false;
        }
        return true;
    }

    override @property size_t talign() nothrow pure const {
        return (void[]).alignof;
    }

    override const(void)[] initializer() const @trusted {
        return (cast(void*) null)[0 .. (void[]).sizeof];
    }
}

class TypeInfo_Tuple : TypeInfo {
    TypeInfo[] elements;
}

class TypeInfo_StaticArray : TypeInfo {
    TypeInfo value;
    size_t len;
    override size_t size() const {
        return value.size * len;
    }

    override const(TypeInfo) next() const {
        return value;
    }

    override bool equals(in void* p1, in void* p2) const {
        size_t sz = value.size;

        for (size_t u = 0; u < len; u++) {
            if (!value.equals(p1 + u * sz, p2 + u * sz)) {
                return false;
            }
        }
        return true;
    }

    override @property size_t talign() nothrow pure const {
        return value.talign;
    }

}

class TypeInfo_Enum : TypeInfo {
    TypeInfo base;
    string name;
    void[] m_init;

    override size_t size() const {
        return base.size;
    }

    override const(TypeInfo) next() const {
        return base.next;
    }

    override bool equals(in void* p1, in void* p2) const {
        return base.equals(p1, p2);
    }

    override @property size_t talign() const {
        return base.talign;
    }

    override void destroy(void* p) const {
        return base.destroy(p);
    }

    override void postblit(void* p) const {
        return base.postblit(p);
    }

    override const(void)[] initializer() const {
        return m_init.length ? m_init : base.initializer();
    }
}

// typeof(null)
class TypeInfo_n : TypeInfo {
const:
pure:
@nogc:
nothrow:
@safe:
    override string toString() {
        return "typeof(null)";
    }

    override size_t getHash(scope const void*) {
        return 0;
    }

    override bool equals(in void*, in void*) {
        return true;
    }

    override @property size_t size() {
        return typeof(null).sizeof;
    }

    override const(void)[] initializer() @trusted {
        return (cast(void*) null)[0 .. size_t.sizeof];
    }
}

/**
 * Array of pairs giving the offset and type information for each
 * member in an aggregate.
 */
struct OffsetTypeInfo {
    size_t offset; /// Offset of member from start of object
    TypeInfo ti; /// TypeInfo for this member
}

class TypeInfo_Axa : TypeInfo_Aa {

}

class TypeInfo_Aya : TypeInfo_Aa {

}

class TypeInfo_Function : TypeInfo {
    override string toString() const pure @trusted {
        return deco;
    }

    override bool opEquals(Object o) const {
        if (this is o)
            return true;
        auto c = cast(const TypeInfo_Function) o;
        return c && this.deco == c.deco;
    }

    // BUG: need to add the rest of the functions

    override @property size_t size() nothrow pure const {
        return 0; // no size for functions
    }

    override const(void)[] initializer() const @safe {
        return null;
    }

    TypeInfo _next;
    override const(TypeInfo) next() nothrow pure inout @nogc {
        return _next;
    }

    /**
    * Mangled function type string
    */
    string deco;
}

class TypeInfo_Delegate : TypeInfo {
    TypeInfo next;
    string deco;
    override @property size_t size() nothrow pure const {
        alias dg = int delegate();
        return dg.sizeof;
    }

    override bool equals(in void* p1, in void* p2) const {
        auto dg1 = *cast(void delegate()*) p1;
        auto dg2 = *cast(void delegate()*) p2;
        return dg1 == dg2;
    }

    override const(void)[] initializer() const @trusted {
        return (cast(void*) null)[0 .. (int delegate()).sizeof];
    }

    override size_t getHash(scope const void* p) @trusted const {
        return hashOf(*cast(const void delegate()*) p);
    }

    override @property size_t talign() nothrow pure const {
        alias dg = int delegate();
        return dg.alignof;
    }
}

//Directly copied from LWDR source.
class TypeInfo_Interface : TypeInfo {
    TypeInfo_Class info;

    override bool equals(in void* p1, in void* p2) const {
        Interface* pi = **cast(Interface***)*cast(void**) p1;
        Object o1 = cast(Object)(*cast(void**) p1 - pi.offset);
        pi = **cast(Interface***)*cast(void**) p2;
        Object o2 = cast(Object)(*cast(void**) p2 - pi.offset);

        return o1 == o2 || (o1 && o1.opCmp(o2) == 0);
    }

    override size_t getHash(scope const void* p) @trusted const {
        if (!*cast(void**) p) {
            return 0;
        }
        Interface* pi = **cast(Interface***)*cast(void**) p;
        Object o = cast(Object)(*cast(void**) p - pi.offset);
        assert(o);
        return o.toHash();
    }

    override const(void)[] initializer() const @trusted {
        return (cast(void*) null)[0 .. Object.sizeof];
    }

    override @property size_t size() nothrow pure const {
        return Object.sizeof;
    }
}

class TypeInfo_Const : TypeInfo {
    override size_t getHash(scope const(void*) p) @trusted const nothrow {
        return base.getHash(p);
    }

    TypeInfo base;
    override size_t size() const {
        return base.size;
    }

    override const(TypeInfo) next() const {
        return base.next;
    }

    override const(void)[] initializer() nothrow pure const {
        return base.initializer();
    }

    override @property size_t talign() nothrow pure const {
        return base.talign;
    }

    override bool equals(in void* p1, in void* p2) const {
        return base.equals(p1, p2);
    }
}

/+
class TypeInfo_Immutable : TypeInfo {
	size_t getHash(in void*) nothrow { return 0; }
	TypeInfo base;
}
+/
class TypeInfo_Invariant : TypeInfo {
    TypeInfo base;
    override size_t getHash(scope const(void*) p) @trusted const nothrow {
        return base.getHash(p);
    }

    override size_t size() const {
        return base.size;
    }

    override const(TypeInfo) next() const {
        return base;
    }
}

class TypeInfo_Shared : TypeInfo {
    override size_t getHash(scope const(void*) p) @trusted const nothrow {
        return base.getHash(p);
    }

    TypeInfo base;
    override size_t size() const {
        return base.size;
    }

    override const(TypeInfo) next() const {
        return base;
    }
}

class TypeInfo_Inout : TypeInfo {
    override size_t getHash(scope const(void*) p) @trusted const nothrow {
        return base.getHash(p);
    }

    TypeInfo base;
    override size_t size() const {
        return base.size;
    }

    override const(TypeInfo) next() const {
        return base;
    }
}

class TypeInfo_Struct : TypeInfo {
    string name;
    void[] m_init;
    @safe pure nothrow {
        size_t function(in void*) xtoHash;
        bool function(in void*, in void*) xopEquals;
        int function(in void*, in void*) xopCmp;
        string function(in void*) xtoString;
    }
    uint m_flags;
    union {
        void function(void*) xdtor;
        void function(void*, const TypeInfo_Struct) xdtorti;
    }

    void function(void*) xpostblit;
    uint align_;
    immutable(void)* rtinfo;
    private struct _memberFunc //? Is it necessary
    {
        union {
            struct  // delegate
            {
                const void* ptr;
                const void* funcptr;
            }

            @safe pure nothrow {
                bool delegate(in void*) xopEquals;
                int delegate(in void*) xopCmp;
            }
        }
    }

    enum StructFlags : uint {
        hasPointers = 0x1,
        isDynamicType = 0x2, // built at runtime, needs type info in xdtor
    }

    override string toString() const {
        return name;
    }

    override size_t size() const {
        return m_init.length;
    }

    override @property uint flags() nothrow pure const @safe @nogc {
        return m_flags;
    }

    override size_t toHash() const {
        return hashOf(this.name);
    }

    override bool opEquals(Object o) const {
        if (this is o)
            return true;
        auto s = cast(const TypeInfo_Struct) o;
        return s && this.name == s.name;
    }

    override size_t getHash(scope const void* p) @trusted pure nothrow const {
        assert(p);
        if (xtoHash) {
            return (*xtoHash)(p);
        } else {
            return hashOf(p[0 .. initializer().length]);
        }
    }

    override bool equals(in void* p1, in void* p2) @trusted const {
        import core.stdc.string : memcmp;
        if (!p1 || !p2)
            return false;
        else if (xopEquals)
            return (*xopEquals)(p1, p2);
        else if (p1 == p2)
            return true;
        else // BUG: relies on the GC not moving objects
            return memcmp(p1, p2, m_init.length) == 0;
    }

    override @property size_t talign() nothrow pure const {
        return align_;
    }

    final override void destroy(void* p) const {
        if (xdtor) {
            if (m_flags & StructFlags.isDynamicType)
                (*xdtorti)(p, this);
            else
                (*xdtor)(p);
        }
    }

    override void postblit(void* p) const {
        if (xpostblit)
            (*xpostblit)(p);
    }

    override const(void)[] initializer() nothrow pure const @safe {
        return m_init;
    }
}