module rt.hooks;

version (WebAssembly) {
    import core.internal.platform.memory;
    import core.stdc.string;

    /++
        Marks the memory block as OK to append in-place if possible.
    +/
    void assumeSafeAppend(T)(T[] arr) {
        auto block = getAllocatedBlock(arr.ptr);
        if (block is null)
            assert(0);

        block.used = arr.length;
    }

    /++
        Marks the memory block associated with this array as unique, meaning
        the runtime is allowed to free the old block immediately instead of
        keeping it around for other lingering slices.

        In real D, the GC would take care of this but here I have to hack it.

        arsd.webasm extension
    +/
    void assumeUniqueReference(T)(T[] arr) {
        auto block = getAllocatedBlock(arr.ptr);
        if (block is null)
            assert(0);

        block.flags |= AllocatedBlock.Flags.unique;
    }

}
