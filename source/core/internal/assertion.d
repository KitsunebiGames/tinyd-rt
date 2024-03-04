module core.internal.assertion;
import core.stdc.stdio;
import core.stdc.stdlib;

extern (C):
version (WebAssembly) {
    void _d_assert(string file, uint line) @trusted @nogc {
        abort();
    }

    void _d_assertp(immutable(char)* file, uint line) {
        abort();
    }

    void _d_assert_msg(string msg, string file, uint line) @trusted @nogc {
        abort();
    }

    noreturn onOutOfMemoryError(void* pretend_sideffect = null) @trusted nothrow @nogc /* dmd @@@BUG11461@@@ */ {
        assert(false, "Out of memory");
    }

    noreturn onOutOfMemoryErrorNoGC() @trusted nothrow @nogc {
        assert(false, "Out of memory");
    }

    void __switch_error(string file, size_t line) @trusted @nogc {
        _d_assert_msg("final switch error", file, cast(uint) line);
    }
} else {
     void _d_assert(string file, uint line) @trusted @nogc {
        printf("Assert Failure: %s : %i", file.ptr, line);
        abort();
    }

    void _d_assertp(immutable(char)* file, uint line) {
        printf("Assert Failure: %s : %i", file, line);
        abort();
    }

    void _d_assert_msg(string msg, string file, uint line) @trusted @nogc {
        printf("Assert Failure: %s %s : %i", msg.ptr, file.ptr, line);
        abort();
    }

    noreturn onOutOfMemoryError(void* pretend_sideffect = null) @trusted nothrow @nogc /* dmd @@@BUG11461@@@ */ {
        assert(false, "Out of memory\0");
    }

    noreturn onOutOfMemoryErrorNoGC() @trusted nothrow @nogc {
        assert(false, "Out of memory\0");
    }

    void __switch_error(string file, size_t line) @trusted @nogc {
        _d_assert_msg("final switch error\0", file, cast(uint) line);
    }
}
