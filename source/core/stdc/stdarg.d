module core.stdc.stdarg;
import gcc.builtins;

T alignUp(size_t alignment = size_t.sizeof, T)(T base) pure {
    enum mask = alignment - 1;
    static assert(alignment > 0 && (alignment & mask) == 0, "alignment must be a power of 2");
    auto b = cast(size_t) base;
    b = (b + mask) & ~mask;
    return cast(T) b;
}

version (BigEndian) {

    // Adjusts a size_t-aligned pointer for types smaller than size_t.
    T* adjustForBigEndian(T)(T* p, size_t size) pure {
        return size >= size_t.sizeof ? p : cast(T*)((cast(void*) p) + (size_t.sizeof - size));
    }
}

version (GNU) {
    alias va_copy = __builtin_va_copy;
    alias va_end = __builtin_va_end;
    void va_arg(T)(ref va_list ap, ref T parmn); // intrinsic
    T va_arg(T)(ref va_list ap); // intrinsic
    void va_start(T)(out va_list ap, ref T parmn);
    alias va_list = __gnuc_va_list;
    alias __gnuc_va_list = __builtin_va_list;
} else version (LDC) {

    pragma(LDC_va_copy)
    void va_copy(out va_list dest, va_list src);

    pragma(LDC_va_end)
    void va_end(va_list ap);

    void va_arg(T)(ref va_list ap, ref T parmn) {
        parmn = va_arg!T(ap);
    }

    T va_arg(T)(ref va_list ap) {
        version (X86) {
            auto p = cast(T*) ap;
            ap += T.sizeof.alignUp;
            return *p;
        } else version (ARM_Any) {
            auto p = cast(T*) ap;
            version (BigEndian)
                static if (T.sizeof < size_t.sizeof)
                    p = adjustForBigEndian(p, T.sizeof);
            ap += T.sizeof.alignUp;
            return *p;
        } else version (PPC_Any) {
            /*
            * The rules are described in the 64bit PowerPC ELF ABI Supplement 1.9,
            * available here:
            * http://refspecs.linuxfoundation.org/ELF/ppc64/PPC-elf64abi-1.9.html#PARAM-PASS
            */

            // Chapter 3.1.4 and 3.2.3: alignment may require the va_list pointer to first
            // be aligned before accessing a value
            if (T.alignof >= 8)
                ap = ap.alignUp!8;
            auto p = cast(T*) ap;
            version (BigEndian)
                static if (T.sizeof < size_t.sizeof)
                    p = adjustForBigEndian(p, T.sizeof);
            ap += T.sizeof.alignUp;
            return *p;
        } else version (LoongArch64) {
            auto p = cast(T*) ap;
            ap += T.sizeof.alignUp;
            return *p;
        } else version (MIPS_Any) {
            auto p = cast(T*) ap;
            version (BigEndian)
                static if (T.sizeof < size_t.sizeof)
                    p = adjustForBigEndian(p, T.sizeof);
            ap += T.sizeof.alignUp;
            return *p;
        } else version (RISCV_Any) {
            static if (T.sizeof > (size_t.sizeof << 1))
                auto p = *cast(T**) ap;
            else {
                static if (T.alignof == (size_t.sizeof << 1))
                    ap = ap.alignUp!(size_t.sizeof << 1);
                auto p = cast(T*) ap;
            }
            ap += T.sizeof.alignUp;
            return *p;
        } else
            static assert(0, "Unsupported platform");
    }

    pragma(LDC_va_start)
    void va_start(T)(out va_list ap, ref T parmn) @nogc;

    version (RISCV_Any) {
        // The va_list type is void*, according to RISCV Calling Convention
        // https://github.com/riscv-non-isa/riscv-elf-psabi-doc/blob/master/riscv-cc.adoc
        alias va_list = void*;
    } else {
        alias va_list = char*; // incl. unknown platforms
    }
}
