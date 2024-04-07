/**
 * The atomic module provides basic support for lock-free
 * concurrent programming.
 *
 * Copyright: Copyright Sean Kelly 2005 - 2016.
 * License:   $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Authors:   Sean Kelly, Alex Rønne Petersen
 * Source:    $(DRUNTIMESRC core/_atomic.d)
 */
module core.internal.atomic;

import gcc.config;
import core.atomic;

private {
    /* Construct a type with a shared tail, and if possible with an unshared
    head. */
    template TailShared(U) if (!is(U == shared)) {
        alias TailShared = .TailShared!(shared U);
    }

    template TailShared(S) if (is(S == shared)) {
        // Get the unshared variant of S.
        static if (is(S U == shared U)) {
        } else
            static assert(false, "Should never be triggered. The `static " ~
                    "if` declares `U` as the unshared version of the shared type " ~
                    "`S`. `S` is explicitly declared as shared, so getting `U` " ~
                    "should always work.");

        static if (is(S : U))
            alias TailShared = U;
        else static if (is(S == struct)) {
            enum implName = () {
                /* Start with "_impl". If S has a field with that name, append
                underscores until the clash is resolved. */
                string name = "_impl";
                string[] fieldNames;
                static foreach (alias field; S.tupleof) {
                    fieldNames ~= __traits(identifier, field);
                }
                static bool canFind(string[] haystack, string needle) {
                    foreach (candidate; haystack) {
                        if (candidate == needle)
                            return true;
                    }
                    return false;
                }

                while (canFind(fieldNames, name))
                    name ~= "_";
                return name;
            }();
            struct TailShared {
                static foreach (i, alias field; S.tupleof) {
                    /* On @trusted: This is casting the field from shared(Foo)
                    to TailShared!Foo. The cast is safe because the field has
                    been loaded and is not shared anymore. */
                    mixin("
                        @trusted @property
                        ref "
                            ~ __traits(identifier, field) ~ "()
                        {
                            alias R = TailShared!(typeof(field));
                            return * cast(R*) &"
                            ~ implName ~ ".tupleof[i];
                        }
                    ");
                }
                mixin("
                    S "
                        ~ implName ~ ";
                    alias "
                        ~ implName ~ " this;
                ");
            }
        } else
            alias TailShared = S;
    }
}

/* NOTE: This file has been patched from the original DMD distribution to
 * work with the GDC compiler. And further patched to work with tinyd-rt
 */
version (GNU) {
    import gcc.builtins;

    T atomicOp(string op, T, V1)(ref T val, V1 mod) pure nothrow @nogc @trusted
            if (__traits(compiles, mixin("*cast(T*)&val" ~ op ~ "mod")) && !is(T == shared)) {
        // binary operators
        //
        // +    -   *   /   %   ^^  &
        // |    ^   <<  >>  >>> ~   in
        // ==   !=  <   <=  >   >=
        static if (op == "+" || op == "-" || op == "*" || op == "/" ||
            op == "%" || op == "^^" || op == "&" || op == "|" ||
            op == "^" || op == "<<" || op == ">>" || op == ">>>" ||
            op == "~" ||  // skip "in"
            op == "==" || op == "!=" || op == "<" || op == "<=" ||
            op == ">" || op == ">=") {
            T get = atomicLoad!(MemoryOrder.raw)(val);
            mixin("return get " ~ op ~ " mod;");
        } else { // assignment operators
            //
            // +=   -=  *=  /=  %=  ^^= &=
            // |=   ^=  <<= >>= >>>=    ~=
            static if (op == "+=" || op == "-=" || op == "*=" || op == "/=" ||
                op == "%=" || op == "^^=" || op == "&=" || op == "|=" ||
                op == "^=" || op == "<<=" || op == ">>=" || op == ">>>=") // skip "~="
                {
                    T get, set;

                    do {
                        get = set = atomicLoad!(MemoryOrder.raw)(val);
                        mixin("set " ~ op ~ " mod;");
                    }
                    while (!cas(&val, get, set));
                    return set;
                }
            else {
                static assert(false, "Operation not supported.");
            }
        }
    }

    TailShared!T atomicOp(string op, T, V1)(ref shared T val, V1 mod) pure nothrow @nogc @trusted
            if (__traits(compiles, mixin("*cast(T*)&val" ~ op ~ "mod"))) {
        // binary operators
        //
        // +    -   *   /   %   ^^  &
        // |    ^   <<  >>  >>> ~   in
        // ==   !=  <   <=  >   >=
        static if (op == "+" || op == "-" || op == "*" || op == "/" ||
            op == "%" || op == "^^" || op == "&" || op == "|" ||
            op == "^" || op == "<<" || op == ">>" || op == ">>>" ||
            op == "~" ||  // skip "in"
            op == "==" || op == "!=" || op == "<" || op == "<=" ||
            op == ">" || op == ">=") {
            TailShared!T get = atomicLoad!(MemoryOrder.raw)(val);
            mixin("return get " ~ op ~ " mod;");
        } else // assignment operators
            //
            // +=   -=  *=  /=  %=  ^^= &=
            // |=   ^=  <<= >>= >>>=    ~=
            static if (op == "+=" || op == "-=" || op == "*=" || op == "/=" ||
                op == "%=" || op == "^^=" || op == "&=" || op == "|=" ||
                op == "^=" || op == "<<=" || op == ">>=" || op == ">>>=") // skip "~="
                {
                    TailShared!T get, set;

                    do {
                        get = set = atomicLoad!(MemoryOrder.raw)(val);
                        mixin("set " ~ op ~ " mod;");
                    }
                    while (!cas(&val, get, set));
                    return set;
                }
            else {
                static assert(false, "Operation not supported.");
            }
    }

    bool cas(T, V1, V2)(shared(T)* here, const V1 ifThis, V2 writeThis) pure nothrow @nogc @safe
            if (!is(T == class) && !is(T U : U*) && __traits(compiles, {
                    *here = writeThis;
                })) {
        return casImpl(here, ifThis, writeThis);
    }

    bool cas(T, V1, V2)(shared(T)* here, const shared(V1) ifThis, shared(V2) writeThis) pure nothrow @nogc @safe
            if (is(T == class) && __traits(compiles, { *here = writeThis; })) {
        return casImpl(here, ifThis, writeThis);
    }

    bool cas(T, V1, V2)(shared(T)* here, const shared(V1)* ifThis, shared(V2)* writeThis) pure nothrow @nogc @safe
            if (is(T U : U*) && __traits(compiles, { *here = writeThis; })) {
        return casImpl(here, ifThis, writeThis);
    }

    private bool casImpl(T, V1, V2)(shared(T)* here, V1 ifThis, V2 writeThis) pure nothrow @nogc @trusted
        if(is(T == shared)) {
        static assert(GNU_Have_Atomics, "cas() not supported on this architecture");
        bool res = void;

        static if (T.sizeof == byte.sizeof) {
            res = __atomic_compare_exchange_1(here, cast(void*)&ifThis, *cast(ubyte*)&writeThis,
                false, MemoryOrder.seq, MemoryOrder.seq);
        } else static if (T.sizeof == short.sizeof) {
            res = __atomic_compare_exchange_2(here, cast(void*)&ifThis, *cast(ushort*)&writeThis,
                false, MemoryOrder.seq, MemoryOrder.seq);
        } else static if (T.sizeof == int.sizeof) {
            res = __atomic_compare_exchange_4(here, cast(void*)&ifThis, *cast(uint*)&writeThis,
                false, MemoryOrder.seq, MemoryOrder.seq);
        } else static if (T.sizeof == long.sizeof && GNU_Have_64Bit_Atomics) {
            res = __atomic_compare_exchange_8(here, cast(void*)&ifThis, *cast(ulong*)&writeThis,
                false, MemoryOrder.seq, MemoryOrder.seq);
        } else static if (GNU_Have_LibAtomic) {
            res = __atomic_compare_exchange(T.sizeof, here, cast(void*)&ifThis, cast(void*)&writeThis,
                MemoryOrder.seq, MemoryOrder.seq);
        } else
            static assert(0, "Invalid template type specified.");

        return res;
    }
    

    bool cas(T, V1, V2)(T* here, const V1 ifThis, V2 writeThis) pure nothrow @nogc @safe
            if (!is(T == class) && !is(T U : U*) && __traits(compiles, {
                    *here = writeThis;
                }) && !is(T == shared)) {
        return casImpl(here, ifThis, writeThis);
    }

    bool cas(T, V1, V2)(T* here, const V1 ifThis, V2 writeThis) pure nothrow @nogc @safe
            if (is(T == class) && __traits(compiles, { *here = writeThis; }) && !is(T == shared)) {
        return casImpl(here, ifThis, writeThis);
    }

    bool cas(T, V1, V2)(T* here, const V1* ifThis, V2* writeThis) pure nothrow @nogc @safe
            if (is(T U : U*) && __traits(compiles, { *here = writeThis; }) && !is(T == shared)) {
        return casImpl(here, ifThis, writeThis);
    }

    private bool casImpl(T, V1, V2)(T* here, V1 ifThis, V2 writeThis) pure nothrow @nogc @trusted 
        if(!is(T == shared)) {
        static assert(GNU_Have_Atomics, "cas() not supported on this architecture");
        bool res = void;

        static if (T.sizeof == byte.sizeof) {
            res = __atomic_compare_exchange_1(cast(shared(T)*)here, cast(void*)&ifThis, *cast(ubyte*)&writeThis,
                false, MemoryOrder.seq, MemoryOrder.seq);
        } else static if (T.sizeof == short.sizeof) {
            res = __atomic_compare_exchange_2(cast(shared(T)*)here, cast(void*)&ifThis, *cast(ushort*)&writeThis,
                false, MemoryOrder.seq, MemoryOrder.seq);
        } else static if (T.sizeof == int.sizeof) {
            res = __atomic_compare_exchange_4(cast(shared(T)*)here, cast(void*)&ifThis, *cast(uint*)&writeThis,
                false, MemoryOrder.seq, MemoryOrder.seq);
        } else static if (T.sizeof == long.sizeof && GNU_Have_64Bit_Atomics) {
            res = __atomic_compare_exchange_8(cast(shared(T)*)here, cast(void*)&ifThis, *cast(ulong*)&writeThis,
                false, MemoryOrder.seq, MemoryOrder.seq);
        } else static if (GNU_Have_LibAtomic) {
            res = __atomic_compare_exchange(T.sizeof, cast(shared(T)*)here, cast(void*)&ifThis, cast(void*)&writeThis,
                MemoryOrder.seq, MemoryOrder.seq);
        } else
            static assert(0, "Invalid template type specified.");

        return res;
    }

    T atomicLoad(MemoryOrder ms = MemoryOrder.seq, T)(ref const T val) pure nothrow @nogc @trusted
            if (!__traits(isFloating, T) && !is(T == shared)) {
        static assert(ms != MemoryOrder.rel, "Invalid MemoryOrder for atomicLoad");
        static assert(__traits(isPOD, T), "argument to atomicLoad() must be POD");
        static assert(GNU_Have_Atomics, "atomicLoad() not supported on this architecture");

        static if (T.sizeof == ubyte.sizeof) {
            ubyte value = __atomic_load_1(cast(shared(const(void))*)&val, ms);
            return *cast(T*)&value;
        } else static if (T.sizeof == ushort.sizeof) {
            ushort value = __atomic_load_2(cast(shared(const(void))*)&val, ms);
            return *cast(T*)&value;
        } else static if (T.sizeof == uint.sizeof) {
            uint value = __atomic_load_4(cast(shared(const(void))*)&val, ms);
            return *cast(T*)&value;
        } else static if (T.sizeof == ulong.sizeof && GNU_Have_64Bit_Atomics) {
            ulong value = __atomic_load_8(cast(shared(const(void))*)&val, ms);
            return *cast(T*)&value;
        } else static if (GNU_Have_LibAtomic) {
            T value;
            __atomic_load(T.sizeof, cast(shared(const(void))*)&val, cast(void*)&value, ms);
            return *cast(T*)&value;
        } else
            static assert(0, "Invalid template type specified.");
    }

    TailShared!T atomicLoad(MemoryOrder ms = MemoryOrder.seq, T)(ref const shared T val) pure nothrow @nogc @trusted
            if (!__traits(isFloating, T)) {
        static assert(ms != MemoryOrder.rel, "Invalid MemoryOrder for atomicLoad");
        static assert(__traits(isPOD, T), "argument to atomicLoad() must be POD");
        static assert(GNU_Have_Atomics, "atomicLoad() not supported on this architecture");

        static if (T.sizeof == ubyte.sizeof) {
            ubyte value = __atomic_load_1(&val, ms);
            return *cast(TailShared!T*)&value;
        } else static if (T.sizeof == ushort.sizeof) {
            ushort value = __atomic_load_2(&val, ms);
            return *cast(TailShared!T*)&value;
        } else static if (T.sizeof == uint.sizeof) {
            uint value = __atomic_load_4(&val, ms);
            return *cast(TailShared!T*)&value;
        } else static if (T.sizeof == ulong.sizeof && GNU_Have_64Bit_Atomics) {
            ulong value = __atomic_load_8(&val, ms);
            return *cast(TailShared!T*)&value;
        } else static if (GNU_Have_LibAtomic) {
            T value;
            __atomic_load(T.sizeof, &val, cast(void*)&value, ms);
            return *cast(TailShared!T*)&value;
        } else
            static assert(0, "Invalid template type specified.");
    }

    void atomicStore(MemoryOrder ms = MemoryOrder.seq, T, V1)(ref shared T val, V1 newval) pure nothrow @nogc @trusted
            if (__traits(compiles, { val = newval; }) && !is(T == shared)) {
        static assert(ms != MemoryOrder.acq, "Invalid MemoryOrder for atomicStore");
        static assert(__traits(isPOD, T), "argument to atomicLoad() must be POD");
        static assert(GNU_Have_Atomics, "atomicStore() not supported on this architecture");

        static if (T.sizeof == ubyte.sizeof) {
            __atomic_store_1(&val, *cast(ubyte*)&newval, ms);
        } else static if (T.sizeof == ushort.sizeof) {
            __atomic_store_2(&val, *cast(ushort*)&newval, ms);
        } else static if (T.sizeof == uint.sizeof) {
            __atomic_store_4(&val, *cast(uint*)&newval, ms);
        } else static if (T.sizeof == ulong.sizeof && GNU_Have_64Bit_Atomics) {
            __atomic_store_8(&val, *cast(ulong*)&newval, ms);
        } else static if (GNU_Have_LibAtomic) {
            __atomic_store(T.sizeof, &val, cast(void*)&newval, ms);
        } else
            static assert(0, "Invalid template type specified.");
    }

    void atomicStore(MemoryOrder ms = MemoryOrder.seq, T, V1)(ref T val, V1 newval) pure nothrow @nogc @trusted
            if (__traits(compiles, { val = newval; })) {
        static assert(ms != MemoryOrder.acq, "Invalid MemoryOrder for atomicStore");
        static assert(__traits(isPOD, T), "argument to atomicLoad() must be POD");
        static assert(GNU_Have_Atomics, "atomicStore() not supported on this architecture");

        static if (T.sizeof == ubyte.sizeof) {
            __atomic_store_1(cast(shared(void)*)&val, *cast(ubyte*)&newval, ms);
        } else static if (T.sizeof == ushort.sizeof) {
            __atomic_store_2(cast(shared(void)*)&val, *cast(ushort*)&newval, ms);
        } else static if (T.sizeof == uint.sizeof) {
            __atomic_store_4(cast(shared(void)*)&val, *cast(uint*)&newval, ms);
        } else static if (T.sizeof == ulong.sizeof && GNU_Have_64Bit_Atomics) {
            __atomic_store_8(cast(shared(void)*)&val, *cast(ulong*)&newval, ms);
        } else static if (GNU_Have_LibAtomic) {
            __atomic_store(T.sizeof, cast(shared(void)*)&val, cast(void*)&newval, ms);
        } else
            static assert(0, "Invalid template type specified.");
    }

    void atomicFence() nothrow @nogc {
        __atomic_thread_fence(MemoryOrder.seq);
    }
}

// This is an ABI adapter that works on all architectures.  It type puns
// floats and doubles to ints and longs, atomically loads them, then puns
// them back.  This is necessary so that they get returned in floating
// point instead of integer registers.
TailShared!T atomicLoad(MemoryOrder ms = MemoryOrder.seq, T)(ref const shared T val) pure nothrow @nogc @trusted
        if (__traits(isFloating, T)) {
    static if (T.sizeof == int.sizeof) {
        static assert(is(T : float));
        auto ptr = cast(const shared int*)&val;
        auto asInt = atomicLoad!(ms)(*ptr);
        return *(cast(typeof(return)*)&asInt);
    } else static if (T.sizeof == long.sizeof) {
        static assert(is(T : double));
        auto ptr = cast(const shared long*)&val;
        auto asLong = atomicLoad!(ms)(*ptr);
        return *(cast(typeof(return)*)&asLong);
    } else {
        static assert(0, "Cannot atomically load 80-bit reals.");
    }
}

// This is an ABI adapter that works on all architectures.  It type puns
// floats and doubles to ints and longs, atomically loads them, then puns
// them back.  This is necessary so that they get returned in floating
// point instead of integer registers.
T atomicLoad(MemoryOrder ms = MemoryOrder.seq, T)(ref const T val) pure nothrow @nogc @trusted
        if (__traits(isFloating, T)) {
    static if (T.sizeof == int.sizeof) {
        static assert(is(T : float));
        auto ptr = cast(const shared int*)&val;
        auto asInt = atomicLoad!(ms)(*ptr);
        return *(cast(typeof(return)*)&asInt);
    } else static if (T.sizeof == long.sizeof) {
        static assert(is(T : double));
        auto ptr = cast(const shared long*)&val;
        auto asLong = atomicLoad!(ms)(*ptr);
        return *(cast(typeof(return)*)&asLong);
    } else {
        static assert(0, "Cannot atomically load 80-bit reals.");
    }
}
