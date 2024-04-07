/**
 * The atomic module provides basic support for lock-free
 * concurrent programming.
 *
 * Copyright: Copyright Sean Kelly 2005 - 2016.
 * License:   $(LINK2 http://www.boost.org/LICENSE_1_0.txt, Boost License 1.0)
 * Authors:   Sean Kelly, Alex Rønne Petersen, Manu Evans
 * Source:    $(DRUNTIMESRC core/_atomic.d)
 */
module core.atomic;

import core.internal.atomic;
import core.internal.attributes : betterC;

version(GNU) version = tinyrt_HasAtomics;

/**
 * Specifies the memory ordering semantics of an atomic operation.
 *
 * See_Also:
 *     $(HTTP en.cppreference.com/w/cpp/atomic/memory_order)
 */
enum MemoryOrder : uint {
    /**
     * Not sequenced.
     * Corresponds to $(LINK2 https://llvm.org/docs/Atomics.html#monotonic, LLVM AtomicOrdering.Monotonic)
     * and C++11/C11 `memory_order_relaxed`.
     */
    raw = 0,
    /**
     * Hoist-load + hoist-store barrier.
     * Corresponds to $(LINK2 https://llvm.org/docs/Atomics.html#acquire, LLVM AtomicOrdering.Acquire)
     * and C++11/C11 `memory_order_acquire`.
     */
    acq = 2,
    /**
     * Sink-load + sink-store barrier.
     * Corresponds to $(LINK2 https://llvm.org/docs/Atomics.html#release, LLVM AtomicOrdering.Release)
     * and C++11/C11 `memory_order_release`.
     */
    rel = 3,
    /**
     * Acquire + release barrier.
     * Corresponds to $(LINK2 https://llvm.org/docs/Atomics.html#acquirerelease, LLVM AtomicOrdering.AcquireRelease)
     * and C++11/C11 `memory_order_acq_rel`.
     */
    acq_rel = 4,
    /**
     * Fully sequenced (acquire + release). Corresponds to
     * $(LINK2 https://llvm.org/docs/Atomics.html#sequentiallyconsistent, LLVM AtomicOrdering.SequentiallyConsistent)
     * and C++11/C11 `memory_order_seq_cst`.
     */
    seq = 5,
}

version(tinyrt_HasAtomics) {
    
    /**
    * Loads 'val' from memory and returns it.  The memory barrier specified
    * by 'ms' is applied to the operation, which is fully sequenced by
    * default.  Valid memory orders are MemoryOrder.raw, MemoryOrder.acq,
    * and MemoryOrder.seq.
    *
    * Params:
    *  val = The target variable.
    *
    * Returns:
    *  The value of 'val'.
    */
    T atomicLoad(MemoryOrder ms = MemoryOrder.seq, T)(ref return scope const T val) pure nothrow @nogc @trusted
        if (!is(T == shared U, U) && !is(T == shared inout U, U) && !is(T == shared const U, U))
    {
        return cast(T)core.internal.atomic.atomicLoad!(ms, T)(val);
    }

    /**
    * Writes 'newval' into 'val'.  The memory barrier specified by 'ms' is
    * applied to the operation, which is fully sequenced by default.
    * Valid memory orders are MemoryOrder.raw, MemoryOrder.rel, and
    * MemoryOrder.seq.
    *
    * Params:
    *  val    = The target variable.
    *  newval = The value to store.
    */
    void atomicStore(MemoryOrder ms = MemoryOrder.seq, T, V)(ref T val, V newval) pure nothrow @nogc @trusted
        if (!is(T == shared) && !is(V == shared))
    {
        import core.internal.traits : hasElaborateCopyConstructor;
        static assert (!hasElaborateCopyConstructor!T, "`T` may not have an elaborate copy: atomic operations override regular copying semantics.");
        core.internal.atomic.atomicStore!ms(val, cast(typeof(val))newval);
    }

    /**
    * Atomically adds `mod` to the value referenced by `val` and returns the value `val` held previously.
    * This operation is both lock-free and atomic.
    *
    * Params:
    *  val = Reference to the value to modify.
    *  mod = The value to add.
    *
    * Returns:
    *  The value held previously by `val`.
    */
    T atomicFetchAdd(MemoryOrder ms = MemoryOrder.seq, T)(ref T val, size_t mod) pure nothrow @nogc @trusted
        if ((__traits(isIntegral, T) || is(T == U*, U)) && !is(T == shared))
    {
        return core.internal.atomic.atomicOp!("+=", T, T)(val, cast(T)mod);
    }

    /// Ditto
    T atomicFetchAdd(MemoryOrder ms = MemoryOrder.seq, T)(ref shared T val, size_t mod) pure nothrow @nogc @trusted
        if (__traits(isIntegral, T) || is(T == U*, U))
    {
        return core.internal.atomic.atomicOp!("+=", T, T)(val, cast(T)mod);
    }

    /**
    * Atomically subtracts `mod` from the value referenced by `val` and returns the value `val` held previously.
    * This operation is both lock-free and atomic.
    *
    * Params:
    *  val = Reference to the value to modify.
    *  mod = The value to subtract.
    *
    * Returns:
    *  The value held previously by `val`.
    */
    T atomicFetchSub(MemoryOrder ms = MemoryOrder.seq, T)(ref T val, size_t mod) pure nothrow @nogc @trusted
        if ((__traits(isIntegral, T) || is(T == U*, U)) && !is(T == shared))
    {
        return core.internal.atomic.atomicOp!("-=", T, T)(val, cast(T)mod);
    }

    // Ditto
    T atomicFetchSub(MemoryOrder ms = MemoryOrder.seq, T)(ref shared T val, size_t mod) pure nothrow @nogc @trusted
        if ((__traits(isIntegral, T) || is(T == U*, U)))
    {
        return core.internal.atomic.atomicOp!("-=", T, T)(val, cast(T)mod);
    }

    /**
    * Exchange `exchangeWith` with the memory referenced by `here`.
    * This operation is both lock-free and atomic.
    *
    * Params:
    *  here         = The address of the destination variable.
    *  exchangeWith = The value to exchange.
    *
    * Returns:
    *  The value held previously by `here`.
    */
    T atomicExchange(MemoryOrder ms = MemoryOrder.seq,T,V)(T* here, V exchangeWith) pure nothrow @nogc @trusted
        if (!is(T == shared) && !is(V == shared))
    {
        // resolve implicit conversions
        T arg = exchangeWith;

        static if (__traits(isFloating, T))
        {
            alias IntTy = IntForFloat!T;
            IntTy r = core.internal.atomic.atomicExchange!ms(cast(IntTy*)here, *cast(IntTy*)&arg);
            return *cast(shared(T)*)&r;
        }
        else
            return core.internal.atomic.atomicExchange!ms(here, arg);
    }

    /// Ditto
    TailShared!T atomicExchange(MemoryOrder ms = MemoryOrder.seq,T,V)(shared(T)* here, V exchangeWith) pure nothrow @nogc @trusted
        if (!is(T == class) && !is(T == interface))
    {
        static if (is (V == shared U, U))
            alias Thunk = U;
        else
        {
            import core.internal.traits : hasUnsharedIndirections;
            static assert(!hasUnsharedIndirections!V, "Copying `exchangeWith` of type `" ~ V.stringof ~ "` to `" ~ shared(T).stringof ~ "` would violate shared.");
            alias Thunk = V;
        }
        return atomicExchange!ms(cast(T*)here, *cast(Thunk*)&exchangeWith);
    }

    /// Ditto
    shared(T) atomicExchange(MemoryOrder ms = MemoryOrder.seq,T,V)(shared(T)* here, shared(V) exchangeWith) pure nothrow @nogc @trusted
        if (is(T == class) || is(T == interface))
    {
        static assert (is (V : T), "Can't assign `exchangeWith` of type `" ~ shared(V).stringof ~ "` to `" ~ shared(T).stringof ~ "`.");

        return cast(shared)core.internal.atomic.atomicExchange!ms(cast(T*)here, cast(V)exchangeWith);
    }
    
    /**
    * Performs either compare-and-set or compare-and-swap (or exchange).
    *
    * There are two categories of overloads in this template:
    * The first category does a simple compare-and-set.
    * The comparison value (`ifThis`) is treated as an rvalue.
    *
    * The second category does a compare-and-swap (a.k.a. compare-and-exchange),
    * and expects `ifThis` to be a pointer type, where the previous value
    * of `here` will be written.
    *
    * This operation is both lock-free and atomic.
    *
    * Params:
    *  here      = The address of the destination variable.
    *  writeThis = The value to store.
    *  ifThis    = The comparison value.
    *
    * Returns:
    *  true if the store occurred, false if not.
    */
    template cas(MemoryOrder succ = MemoryOrder.seq, MemoryOrder fail = MemoryOrder.seq)
    {
        /// Compare-and-set for non-shared values
        bool cas(T, V1, V2)(T* here, V1 ifThis, V2 writeThis) pure nothrow @nogc @trusted
        if (!is(T == shared) && is(T : V1))
        in (atomicPtrIsProperlyAligned(here), "Argument `here` is not properly aligned")
        {
            // resolve implicit conversions
            const T arg1 = ifThis;
            T arg2 = writeThis;

            static if (__traits(isFloating, T))
            {
                alias IntTy = IntForFloat!T;
                return atomicCompareExchangeStrongNoResult!(succ, fail)(
                    cast(IntTy*)here, *cast(IntTy*)&arg1, *cast(IntTy*)&arg2);
            }
            else
                return atomicCompareExchangeStrongNoResult!(succ, fail)(here, arg1, arg2);
        }
    }

    /// Compare-and-set for shared value type
    bool cas(T, V1, V2)(shared(T)* here, V1 ifThis, V2 writeThis) pure nothrow @nogc @trusted
    if (!is(T == class) && (is(T : V1) || is(shared T : V1)))
    in (atomicPtrIsProperlyAligned(here), "Argument `here` is not properly aligned")
    {
        static if (is (V1 == shared U1, U1))
            alias Thunk1 = U1;
        else
            alias Thunk1 = V1;
        static if (is (V2 == shared U2, U2))
            alias Thunk2 = U2;
        else
        {
            import core.internal.traits : hasUnsharedIndirections;
            static assert(!hasUnsharedIndirections!V2,
                          "Copying `" ~ V2.stringof ~ "* writeThis` to `" ~
                          shared(T).stringof ~ "* here` would violate shared.");
            alias Thunk2 = V2;
        }
        return cas(cast(T*)here, *cast(Thunk1*)&ifThis, *cast(Thunk2*)&writeThis);
    }

    /// Compare-and-set for `shared` reference type (`class`)
    bool cas(T, V1, V2)(shared(T)* here, shared(V1) ifThis, shared(V2) writeThis)
    pure nothrow @nogc @trusted
    if (is(T == class))
    in (atomicPtrIsProperlyAligned(here), "Argument `here` is not properly aligned")
    {
        return atomicCompareExchangeStrongNoResult!(succ, fail)(
            cast(T*)here, cast(V1)ifThis, cast(V2)writeThis);
    }

    /// Compare-and-exchange for non-`shared` types
    bool cas(T, V)(T* here, T* ifThis, V writeThis) pure nothrow @nogc @trusted
    if (!is(T == shared) && !is(V == shared))
    in (atomicPtrIsProperlyAligned(here), "Argument `here` is not properly aligned")
    {
        // resolve implicit conversions
        T arg1 = writeThis;

        static if (__traits(isFloating, T))
        {
            alias IntTy = IntForFloat!T;
            return atomicCompareExchangeStrong!(succ, fail)(
                cast(IntTy*)here, cast(IntTy*)ifThis, *cast(IntTy*)&writeThis);
        }
        else
            return atomicCompareExchangeStrong!(succ, fail)(here, ifThis, writeThis);
    }

    /// Compare and exchange for mixed-`shared`ness types
    bool cas(T, V1, V2)(shared(T)* here, V1* ifThis, V2 writeThis) pure nothrow @nogc @trusted
    if (!is(T == class) && (is(T : V1) || is(shared T : V1)))
    in (atomicPtrIsProperlyAligned(here), "Argument `here` is not properly aligned")
    {
        static if (is (V1 == shared U1, U1))
            alias Thunk1 = U1;
        else
        {
            import core.internal.traits : hasUnsharedIndirections;
            static assert(!hasUnsharedIndirections!V1,
                          "Copying `" ~ shared(T).stringof ~ "* here` to `" ~
                          V1.stringof ~ "* ifThis` would violate shared.");
            alias Thunk1 = V1;
        }
        static if (is (V2 == shared U2, U2))
            alias Thunk2 = U2;
        else
        {
            import core.internal.traits : hasUnsharedIndirections;
            static assert(!hasUnsharedIndirections!V2,
                          "Copying `" ~ V2.stringof ~ "* writeThis` to `" ~
                          shared(T).stringof ~ "* here` would violate shared.");
            alias Thunk2 = V2;
        }
        static assert (is(T : Thunk1),
                       "Mismatching types for `here` and `ifThis`: `" ~
                       shared(T).stringof ~ "` and `" ~ V1.stringof ~ "`.");
        return cas(cast(T*)here, cast(Thunk1*)ifThis, *cast(Thunk2*)&writeThis);
    }

    /// Compare-and-exchange for `class`
    bool cas(T, V)(shared(T)* here, shared(T)* ifThis, shared(V) writeThis)
    pure nothrow @nogc @trusted
    if (is(T == class))
    in (atomicPtrIsProperlyAligned(here), "Argument `here` is not properly aligned")
    {
        return atomicCompareExchangeStrong!(succ, fail)(
            cast(T*)here, cast(T*)ifThis, cast(V)writeThis);
    }

    /**
    * Stores 'writeThis' to the memory referenced by 'here' if the value
    * referenced by 'here' is equal to 'ifThis'.
    * The 'weak' version of cas may spuriously fail. It is recommended to
    * use `casWeak` only when `cas` would be used in a loop.
    * This operation is both
    * lock-free and atomic.
    *
    * Params:
    *  here      = The address of the destination variable.
    *  writeThis = The value to store.
    *  ifThis    = The comparison value.
    *
    * Returns:
    *  true if the store occurred, false if not.
    */
    bool casWeak(MemoryOrder succ = MemoryOrder.seq,MemoryOrder fail = MemoryOrder.seq,T,V1,V2)(T* here, V1 ifThis, V2 writeThis) pure nothrow @nogc @trusted
        if (!is(T == shared) && is(T : V1))
    in (atomicPtrIsProperlyAligned(here), "Argument `here` is not properly aligned")
    {
        // resolve implicit conversions
        T arg1 = ifThis;
        T arg2 = writeThis;

        static if (__traits(isFloating, T))
        {
            alias IntTy = IntForFloat!T;
            return atomicCompareExchangeWeakNoResult!(succ, fail)(cast(IntTy*)here, *cast(IntTy*)&arg1, *cast(IntTy*)&arg2);
        }
        else
            return atomicCompareExchangeWeakNoResult!(succ, fail)(here, arg1, arg2);
    }

    /// Ditto
    bool casWeak(MemoryOrder succ = MemoryOrder.seq,MemoryOrder fail = MemoryOrder.seq,T,V1,V2)(shared(T)* here, V1 ifThis, V2 writeThis) pure nothrow @nogc @trusted
        if (!is(T == class) && (is(T : V1) || is(shared T : V1)))
    in (atomicPtrIsProperlyAligned(here), "Argument `here` is not properly aligned")
    {
        static if (is (V1 == shared U1, U1))
            alias Thunk1 = U1;
        else
            alias Thunk1 = V1;
        static if (is (V2 == shared U2, U2))
            alias Thunk2 = U2;
        else
        {
            import core.internal.traits : hasUnsharedIndirections;
            static assert(!hasUnsharedIndirections!V2, "Copying `" ~ V2.stringof ~ "* writeThis` to `" ~ shared(T).stringof ~ "* here` would violate shared.");
            alias Thunk2 = V2;
        }
        return casWeak!(succ, fail)(cast(T*)here, *cast(Thunk1*)&ifThis, *cast(Thunk2*)&writeThis);
    }

    /// Ditto
    bool casWeak(MemoryOrder succ = MemoryOrder.seq,MemoryOrder fail = MemoryOrder.seq,T,V1,V2)(shared(T)* here, shared(V1) ifThis, shared(V2) writeThis) pure nothrow @nogc @trusted
        if (is(T == class))
    in (atomicPtrIsProperlyAligned(here), "Argument `here` is not properly aligned")
    {
        return atomicCompareExchangeWeakNoResult!(succ, fail)(cast(T*)here, cast(V1)ifThis, cast(V2)writeThis);
    }

    /**
    * Stores 'writeThis' to the memory referenced by 'here' if the value
    * referenced by 'here' is equal to the value referenced by 'ifThis'.
    * The prior value referenced by 'here' is written to `ifThis` and
    * returned to the user.
    * The 'weak' version of cas may spuriously fail. It is recommended to
    * use `casWeak` only when `cas` would be used in a loop.
    * This operation is both lock-free and atomic.
    *
    * Params:
    *  here      = The address of the destination variable.
    *  writeThis = The value to store.
    *  ifThis    = The address of the value to compare, and receives the prior value of `here` as output.
    *
    * Returns:
    *  true if the store occurred, false if not.
    */
    bool casWeak(MemoryOrder succ = MemoryOrder.seq,MemoryOrder fail = MemoryOrder.seq,T,V)(T* here, T* ifThis, V writeThis) pure nothrow @nogc @trusted
        if (!is(T == shared S, S) && !is(V == shared U, U))
    in (atomicPtrIsProperlyAligned(here), "Argument `here` is not properly aligned")
    {
        // resolve implicit conversions
        T arg1 = writeThis;

        static if (__traits(isFloating, T))
        {
            alias IntTy = IntForFloat!T;
            return atomicCompareExchangeWeak!(succ, fail)(cast(IntTy*)here, cast(IntTy*)ifThis, *cast(IntTy*)&writeThis);
        }
        else
            return atomicCompareExchangeWeak!(succ, fail)(here, ifThis, writeThis);
    }

    /// Ditto
    bool casWeak(MemoryOrder succ = MemoryOrder.seq,MemoryOrder fail = MemoryOrder.seq,T,V1,V2)(shared(T)* here, V1* ifThis, V2 writeThis) pure nothrow @nogc @trusted
        if (!is(T == class) && (is(T : V1) || is(shared T : V1)))
    in (atomicPtrIsProperlyAligned(here), "Argument `here` is not properly aligned")
    {
        static if (is (V1 == shared U1, U1))
            alias Thunk1 = U1;
        else
        {
            import core.internal.traits : hasUnsharedIndirections;
            static assert(!hasUnsharedIndirections!V1, "Copying `" ~ shared(T).stringof ~ "* here` to `" ~ V1.stringof ~ "* ifThis` would violate shared.");
            alias Thunk1 = V1;
        }
        static if (is (V2 == shared U2, U2))
            alias Thunk2 = U2;
        else
        {
            import core.internal.traits : hasUnsharedIndirections;
            static assert(!hasUnsharedIndirections!V2, "Copying `" ~ V2.stringof ~ "* writeThis` to `" ~ shared(T).stringof ~ "* here` would violate shared.");
            alias Thunk2 = V2;
        }
        static assert (is(T : Thunk1), "Mismatching types for `here` and `ifThis`: `" ~ shared(T).stringof ~ "` and `" ~ V1.stringof ~ "`.");
        return casWeak!(succ, fail)(cast(T*)here, cast(Thunk1*)ifThis, *cast(Thunk2*)&writeThis);
    }

    /// Ditto
    bool casWeak(MemoryOrder succ = MemoryOrder.seq,MemoryOrder fail = MemoryOrder.seq,T,V)(shared(T)* here, shared(T)* ifThis, shared(V) writeThis) pure nothrow @nogc @trusted
        if (is(T == class))
    in (atomicPtrIsProperlyAligned(here), "Argument `here` is not properly aligned")
    {
        return atomicCompareExchangeWeak!(succ, fail)(cast(T*)here, cast(T*)ifThis, cast(V)writeThis);
    }

    /**
    * Inserts a full load/store memory fence (on platforms that need it). This ensures
    * that all loads and stores before a call to this function are executed before any
    * loads and stores after the call.
    */
    void atomicFence(MemoryOrder order = MemoryOrder.seq)() pure nothrow @nogc @safe
    {
        core.internal.atomic.atomicFence!order();
    }
}
