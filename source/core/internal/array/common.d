module core.internal.array.common;
import core.internal.assertion;
import core.internal.objutils;
import core.stdc.stdlib : abort;
import core.stdc.string : memcpy, memset;
import core.internal.traits;

import mem = core.internal.platform.memory;
import rt.hooks;

extern (C):
byte[] _d_arrayappendcTX(const TypeInfo ti, ref byte[] px, size_t n) @trusted nothrow {
	auto elemSize = ti.next.size;
	auto newLength = n + px.length;
	auto newSize = newLength * elemSize;
	//import std.stdio; writeln(newSize, " ", newLength);
	ubyte* ptr;
	bool hasReallocated = false;
	if (px.ptr is null)
		ptr = cast(ubyte*) mem.malloc(newSize);
	else {
		// FIXME: anti-stomping by checking length == used   
		hasReallocated = true;
		ptr = mem.realloc(cast(ubyte[]) px, newSize).ptr;
	}
	auto ns = ptr[0 .. newSize];
	auto op = px.ptr;
	auto ol = px.length * elemSize;

	foreach (i, b; op[0 .. ol])
		ns[i] = b;

	(cast(size_t*)(&px))[0] = newLength;
	(cast(void**)(&px))[1] = ns.ptr;
	return px;
}

template _d_arrayappendcTXImpl(Tarr : T[], T) {
	alias _d_arrayappendcTX = ._d_arrayappendcTX!(Tarr, T);
}

ref Tarr _d_arrayappendcTX(Tarr : T[], T)(return ref scope Tarr px, size_t n) @trusted nothrow pure {
	// needed for CTFE: https://github.com/dlang/druntime/pull/3870#issuecomment-1178800718
	pragma(inline, false);
	auto ti = typeid(Tarr);

	alias pureArrayAppendcTX = extern (C) @trusted nothrow pure byte[]function(
		const TypeInfo ti, ref byte[] px, size_t n);

	auto arrayAppendcTX = cast(pureArrayAppendcTX)&_d_arrayappendcTX;

	// _d_arrayappendcTX takes the `px` as a ref byte[], but its length
	// should still be the original length
	auto pxx = (cast(byte*) px.ptr)[0 .. px.length];
	arrayAppendcTX(ti, pxx, n);
	px = (cast(T*) pxx.ptr)[0 .. pxx.length];

	return px;
}

ref Tarr _d_arrayappendT(Tarr : T[], T)(return ref scope Tarr x, scope Tarr y) @trusted pure {
	auto length = x.length;

	alias pure_d_arrayappendcTX = pure nothrow @trusted ref Tarr function(
		return ref scope Tarr px, size_t n);
	auto arrayAppendcTX = cast(pure_d_arrayappendcTX)&_d_arrayappendcTX!Tarr;

	arrayAppendcTX(x, y.length);
	memcpy(cast(Unqual!T*) x.ptr + length * T.sizeof, y.ptr, y.length * T.sizeof);

	// do postblit
	//__doPostblit(x.ptr + length * sizeelem, y.length * sizeelem, tinext);
	return x;
}

void[] _d_arrayappendT(const TypeInfo ti, ref byte[] x, byte[] y) {
	auto length = x.length;
	auto tinext = ti.next;
	auto sizeelem = tinext.size; // array element size
	_d_arrayappendcTX(ti, x, y.length);
	memcpy(x.ptr + length * sizeelem, y.ptr, y.length * sizeelem);
	return x;
}

void __ArrayDtor(T)(scope T[] a) {
	foreach_reverse (ref T e; a)
		e.__xdtor();
}

TTo[] __ArrayCast(TFrom, TTo)(return scope TFrom[] from) {
	const fromSize = from.length * TFrom.sizeof;
	const toLength = fromSize / TTo.sizeof;

	if ((fromSize % TTo.sizeof) != 0) {
		//onArrayCastError(TFrom.stringof, fromSize, TTo.stringof, toLength * TTo.sizeof);
		import arsd.webassembly;

		abort();
	}

	struct Array {
		size_t length;
		void* ptr;
	}

	auto a = cast(Array*)&from;
	a.length = toLength; // jam new length
	return *cast(TTo[]*) a;
}

// basic array support {

template _arrayOp(Args...) {
	import core.internal.array.operations;

	alias _arrayOp = arrayOp!Args;
}

void _d_array_slice_copy(void* dst, size_t dstlen, void* src, size_t srclen, size_t elemsz) {
	auto d = cast(ubyte*) dst;
	auto s = cast(ubyte*) src;
	auto len = dstlen * elemsz;

	while (len) {
		*d = *s;
		d++;
		s++;
		len--;
	}

}

void reserve(T)(ref T[] arr, size_t length) @trusted {
	arr = (cast(T*)(mem.malloc(length * T.sizeof).ptr))[0 .. 0];
}

void _d_arraybounds(string file, size_t line) {

	version (WebAssembly)
		arsd.webassembly.eval(
			q{ console.error("Range error: " + $0 + ":" + $1 )},
			file, line);
	else version (CustomRuntimePrinter)
		customRuntimePrinter("Range Error: ", file, ":", line);
	abort();
}

/// Called when an out of range slice of an array is created
void _d_arraybounds_slice(string file, uint line, size_t lwr, size_t upr, size_t length) {
	version (WebAssembly)
		arsd.webassembly.eval(
			q{ console.error("Range error: " + $0 + ":" + $1 + " [" + $2 + ".." + $3 + "] <> " + $4)},
			file, line, lwr, upr, length);
	else version (CustomRuntimePrinter)
		customRuntimePrinter("Range Error: ", file, ":", line, " [", lwr, "..", upr, "] <> ", length);
	abort();
}

/// Called when an out of range array index is accessed
void _d_arraybounds_index(string file, uint line, size_t index, size_t length) {
	version (WebAssembly)
		arsd.webassembly.eval(
			q{ console.error("Array index " + $0  + " out of bounds '[0.."+$1+"]' " + $2 + ":" + $3)},
			index, length, file, line);
	else version (CustomRuntimePrinter)
		customRuntimePrinter("Array index: ", index, " out of bounds '[0..", length, "]'", file, ":", line);
	abort();
}

T[] _d_newarrayU(T)(size_t length, bool isShared = false) pure @trusted {
	alias PureM = ubyte[]function(size_t sz, string file = __FILE__, size_t line = __LINE__) pure @trusted nothrow;
	PureM pureMalloc = cast(PureM)&malloc;
	return (cast(T*) pureMalloc(length * T.sizeof).ptr)[0 .. length];
}

T[] _d_newarrayT(T)(size_t length, bool isShared = false) pure @trusted {
	auto arr = _d_newarrayU!T(length);
	(cast(byte[]) arr)[] = 0;
	return arr;
}

Tret _d_arraycatnTX(Tret, Tarr...)(auto ref Tarr froms) @trusted {
	import core.internal.traits : hasElaborateCopyConstructor, Unqual;
	import core.lifetime : copyEmplace;

	Tret res;
	size_t totalLen;

	alias T = typeof(res[0]);
	enum elemSize = T.sizeof;
	enum hasPostblit = __traits(hasPostblit, T);

	static foreach (from; froms)
		static if (is(typeof(from) : T))
			totalLen++;
		else
			totalLen += from.length;

	if (totalLen == 0)
		return res;

	_d_arraysetlengthTImpl!(typeof(res))._d_arraysetlengthT(res, totalLen);

	/* Currently, if both a postblit and a cpctor are defined, the postblit is
     * used. If this changes, the condition below will have to be adapted.
     */
	static if (hasElaborateCopyConstructor!T && !hasPostblit) {
		size_t i = 0;
		foreach (ref from; froms)
			static if (is(typeof(from) : T))
				copyEmplace(cast(T) from, res[i++]);
			else {
				if (from.length)
					foreach (ref elem; from)
						copyEmplace(cast(T) elem, res[i++]);
			}
	} else {
		auto resptr = cast(Unqual!T*) res;
		foreach (ref from; froms)
			static if (is(typeof(from) : T))
				memcpy(resptr++, cast(Unqual!T*)&from, elemSize);
			else {
				const len = from.length;
				if (len) {
					memcpy(resptr, cast(Unqual!T*) from, len * elemSize);
					resptr += len;
				}
			}

		static if (hasPostblit)
			foreach (ref elem; res)
				(cast() elem).__xpostblit();
	}

	return res;
}

void[] _d_arrayappendcd(ref byte[] x, dchar c) {
	// c could encode into from 1 to 4 characters
	char[4] buf = void;
	byte[] appendthis; // passed to appendT
	if (c <= 0x7F) {
		buf.ptr[0] = cast(char) c;
		appendthis = (cast(byte*) buf.ptr)[0 .. 1];
	} else if (c <= 0x7FF) {
		buf.ptr[0] = cast(char)(0xC0 | (c >> 6));
		buf.ptr[1] = cast(char)(0x80 | (c & 0x3F));
		appendthis = (cast(byte*) buf.ptr)[0 .. 2];
	} else if (c <= 0xFFFF) {
		buf.ptr[0] = cast(char)(0xE0 | (c >> 12));
		buf.ptr[1] = cast(char)(0x80 | ((c >> 6) & 0x3F));
		buf.ptr[2] = cast(char)(0x80 | (c & 0x3F));
		appendthis = (cast(byte*) buf.ptr)[0 .. 3];
	} else if (c <= 0x10FFFF) {
		buf.ptr[0] = cast(char)(0xF0 | (c >> 18));
		buf.ptr[1] = cast(char)(0x80 | ((c >> 12) & 0x3F));
		buf.ptr[2] = cast(char)(0x80 | ((c >> 6) & 0x3F));
		buf.ptr[3] = cast(char)(0x80 | (c & 0x3F));
		appendthis = (cast(byte*) buf.ptr)[0 .. 4];
	} else
		assert(false, "Could not append dchar"); // invalid utf character - should we throw an exception instead?

	//
	// TODO: This always assumes the array type is shared, because we do not
	// get a typeinfo from the compiler.  Assuming shared is the safest option.
	// Once the compiler is fixed, the proper typeinfo should be forwarded.
	//
	return _d_arrayappendT(typeid(shared char[]), x, appendthis);
}

template _d_arraysetlengthTImpl(Tarr : T[], T) {
	size_t _d_arraysetlengthT(return scope ref Tarr arr, size_t newlength) @trusted pure {
		auto orig = arr;

		if (newlength <= arr.length) {
			arr = arr[0 .. newlength];
		} else {
			auto ptr = cast(T*) mem.pureRealloc(cast(ubyte[]) arr, newlength * T.sizeof);
			arr = ptr[0 .. newlength];
			if (orig !is null) {
				static if (is(Tarr == string))
					(cast(char[]) arr)[0 .. orig.length] = orig[];
				else static if (is(Tarr == wstring))
					(cast(wchar[]) arr)[0 .. orig.length] = orig[];
				else static if (is(Tarr == dstring))
					(cast(dchar[]) arr)[0 .. orig.length] = orig[];
				else
					arr[0 .. orig.length] = orig[];
			}
		}

		return newlength;
	}
}

void[] _d_arraysetlengthT(const TypeInfo ti, size_t newlength, void[]* p)
in {
	assert(ti);
	assert(!(*p).length || (*p).ptr);
}
do {
	import core.internal.objutils;

	if (newlength <= (*p).length) {
		*p = (*p)[0 .. newlength];
		void* newdata = (*p).ptr;
		return newdata[0 .. newlength];
	}
	auto tinext = ti.next;
	size_t sizeelem = tinext.size;

	/* Calculate: newsize = newlength * sizeelem
     */
	bool overflow = false;
	import core.checkedint : mulu;

	const size_t newsize = mulu(sizeelem, newlength, overflow);
	if (overflow)
		onOutOfMemoryError();

	if (!(*p).ptr) {
		// pointer was null, need to allocate
		auto info = mem.malloc(newsize);
		memset(info.ptr, 0, newsize);
		*p = info[0 .. newlength];
		return *p;
	}

	const size_t size = (*p).length * sizeelem;

	/* Attempt to extend past the end of the existing array.
     * If not possible, allocate new space for entire array and copy.
     */
	auto ptr = mem.pureRealloc(cast(ubyte[])*p, newsize);
	ptr[0 .. size] = cast(ubyte[]) p.ptr[0 .. size];

	/* Do postblit processing, as we are making a copy and the
    * original array may have references.
    * Note that this may throw.
    */
	__doPostblit(p.ptr, size, tinext);

	// Initialize the unused portion of the newly allocated space
	memset(p.ptr + size, 0, newsize - size);
	return *p;
}

void[] _d_arraysetlengthiT(const TypeInfo ti, size_t newlength, void[]* p)
in {
	assert(!(*p).length || (*p).ptr);
}
do {
	if (newlength <= (*p).length) {
		*p = (*p)[0 .. newlength];
		void* newdata = (*p).ptr;
		return newdata[0 .. newlength];
	}
	auto tinext = ti.next;
	size_t sizeelem = tinext.size;

	import core.checkedint : mulu;

	bool overflow;
	const size_t newsize = mulu(sizeelem, newlength, overflow);
	if (overflow)
		onOutOfMemoryError();

	static void doInitialize(void* start, void* end, const void[] initializer) {
		if (initializer.length == 1) {
			memset(start, *(cast(ubyte*) initializer.ptr), end - start);
		} else {
			auto q = initializer.ptr;
			immutable initsize = initializer.length;
			for (; start < end; start += initsize) {
				memcpy(start, q, initsize);
			}
		}
	}

	if (!(*p).ptr) {
		// pointer was null, need to allocate
		auto info = mem.malloc(newsize);
		doInitialize(info.ptr, info.ptr + newsize, tinext.initializer);
		*p = info[0 .. newlength];
		return *p;
	}

	const size_t size = (*p).length * sizeelem;

	/* Attempt to extend past the end of the existing array.
     * If not possible, allocate new space for entire array and copy.
     */
	auto ptr = mem.pureRealloc(cast(ubyte[])*p, newsize);
	ptr[0 .. size] = cast(ubyte[]) p.ptr[0 .. size];

	/* Do postblit processing, as we are making a copy and the
    * original array may have references.
    * Note that this may throw.
    */
	__doPostblit(p.ptr, size, tinext);

	// Initialize the unused portion of the newly allocated space
	doInitialize(p.ptr + size, p.ptr + newsize, tinext.initializer);
	return *p;
}
