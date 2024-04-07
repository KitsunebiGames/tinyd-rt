// Written in the D programming language.
/**
This is a submodule of $(MREF std, algorithm).
It contains generic searching algorithms.

$(SCRIPT inhibitQuickIndex = 1;)
$(BOOKTABLE Cheat Sheet,
$(TR $(TH Function Name) $(TH Description))
$(T2 all,
        `all!"a > 0"([1, 2, 3, 4])` returns `true` because all elements
        are positive)
$(T2 any,
        `any!"a > 0"([1, 2, -3, -4])` returns `true` because at least one
        element is positive)
$(T2 balancedParens,
        `balancedParens("((1 + 1) / 2)")` returns `true` because the
        string has balanced parentheses.)
$(T2 boyerMooreFinder,
        `find("hello world", boyerMooreFinder("or"))` returns `"orld"`
        using the $(LINK2 https://en.wikipedia.org/wiki/Boyer%E2%80%93Moore_string_search_algorithm,
        Boyer-Moore _algorithm).)
$(T2 canFind,
        `canFind("hello world", "or")` returns `true`.)
$(T2 count,
        Counts elements that are equal to a specified value or satisfy a
        predicate.  `count([1, 2, 1], 1)` returns `2` and
        `count!"a < 0"([1, -3, 0])` returns `1`.)
$(T2 countUntil,
        `countUntil(a, b)` returns the number of steps taken in `a` to
        reach `b`; for example, `countUntil("hello!", "o")` returns
        `4`.)
$(T2 commonPrefix,
        `commonPrefix("parakeet", "parachute")` returns `"para"`.)
$(T2 endsWith,
        `endsWith("rocks", "ks")` returns `true`.)
$(T2 find,
        `find("hello world", "or")` returns `"orld"` using linear search.
        (For binary search refer to $(REF SortedRange, std,range).))
$(T2 findAdjacent,
        `findAdjacent([1, 2, 3, 3, 4])` returns the subrange starting with
        two equal adjacent elements, i.e. `[3, 3, 4]`.)
$(T2 findAmong,
        `findAmong("abcd", "qcx")` returns `"cd"` because `'c'` is
        among `"qcx"`.)
$(T2 findSkip,
        If `a = "abcde"`, then `findSkip(a, "x")` returns `false` and
        leaves `a` unchanged, whereas `findSkip(a, "c")` advances `a`
        to `"de"` and returns `true`.)
$(T2 findSplit,
        `findSplit("abcdefg", "de")` returns the three ranges `"abc"`,
        `"de"`, and `"fg"`.)
$(T2 findSplitAfter,
        `findSplitAfter("abcdefg", "de")` returns the two ranges
        `"abcde"` and `"fg"`.)
$(T2 findSplitBefore,
        `findSplitBefore("abcdefg", "de")` returns the two ranges `"abc"`
        and `"defg"`.)
$(T2 minCount,
        `minCount([2, 1, 1, 4, 1])` returns `tuple(1, 3)`.)
$(T2 maxCount,
        `maxCount([2, 4, 1, 4, 1])` returns `tuple(4, 2)`.)
$(T2 minElement,
        Selects the minimal element of a range.
        `minElement([3, 4, 1, 2])` returns `1`.)
$(T2 maxElement,
        Selects the maximal element of a range.
        `maxElement([3, 4, 1, 2])` returns `4`.)
$(T2 minIndex,
        Index of the minimal element of a range.
        `minElement([3, 4, 1, 2])` returns `2`.)
$(T2 maxIndex,
        Index of the maximal element of a range.
        `maxElement([3, 4, 1, 2])` returns `1`.)
$(T2 minPos,
        `minPos([2, 3, 1, 3, 4, 1])` returns the subrange `[1, 3, 4, 1]`,
        i.e., positions the range at the first occurrence of its minimal
        element.)
$(T2 maxPos,
        `maxPos([2, 3, 1, 3, 4, 1])` returns the subrange `[4, 1]`,
        i.e., positions the range at the first occurrence of its maximal
        element.)
$(T2 skipOver,
        Assume `a = "blah"`. Then `skipOver(a, "bi")` leaves `a`
        unchanged and returns `false`, whereas `skipOver(a, "bl")`
        advances `a` to refer to `"ah"` and returns `true`.)
$(T2 startsWith,
        `startsWith("hello, world", "hello")` returns `true`.)
$(T2 until,
        Lazily iterates a range until a specific value is found.)
)

Copyright: Andrei Alexandrescu 2008-.

License: $(HTTP boost.org/LICENSE_1_0.txt, Boost License 1.0).

Authors: $(HTTP erdani.com, Andrei Alexandrescu)

Source: $(PHOBOSSRC std/algorithm/searching.d)

Macros:
T2=$(TR $(TDNW $(LREF $1)) $(TD $+))
 */
module std.algorithm.searching;

import std.functional;
import std.traits;


/**
 * Sets up Boyer-Moore matching for use with `find` below.
 * By default, elements are compared for equality.
 *
 * `BoyerMooreFinder` allocates GC memory.
 *
 * Params:
 * pred = Predicate used to compare elements.
 * needle = A random-access range with length and slicing.
 *
 * Returns:
 * An instance of `BoyerMooreFinder` that can be used with `find()` to
 * invoke the Boyer-Moore matching algorithm for finding of `needle` in a
 * given haystack.
 */
struct BoyerMooreFinder(alias pred, Range)
{
private:
    size_t[] skip;                              // GC allocated
    ptrdiff_t[ElementType!(Range)] occ;         // GC allocated
    Range needle;

    ptrdiff_t occurrence(ElementType!(Range) c) scope
    {
        auto p = c in occ;
        return p ? *p : -1;
    }

/*
This helper function checks whether the last "portion" bytes of
"needle" (which is "nlen" bytes long) exist within the "needle" at
offset "offset" (counted from the end of the string), and whether the
character preceding "offset" is not a match.  Notice that the range
being checked may reach beyond the beginning of the string. Such range
is ignored.
 */
    static bool needlematch(R)(R needle,
                              size_t portion, size_t offset)
    {
        import std.algorithm.comparison : equal;
        ptrdiff_t virtual_begin = needle.length - offset - portion;
        ptrdiff_t ignore = 0;
        if (virtual_begin < 0)
        {
            ignore = -virtual_begin;
            virtual_begin = 0;
        }
        if (virtual_begin > 0
            && needle[virtual_begin - 1] == needle[$ - portion - 1])
            return 0;

        immutable delta = portion - ignore;
        return equal(needle[needle.length - delta .. needle.length],
                needle[virtual_begin .. virtual_begin + delta]);
    }

public:
    ///
    this(Range needle)
    {
        if (!needle.length) return;
        this.needle = needle;
        /* Populate table with the analysis of the needle */
        /* But ignoring the last letter */
        foreach (i, n ; needle[0 .. $ - 1])
        {
            this.occ[n] = i;
        }
        /* Preprocess #2: init skip[] */
        /* Note: This step could be made a lot faster.
         * A simple implementation is shown here. */
        this.skip = new size_t[needle.length];
        foreach (a; 0 .. needle.length)
        {
            size_t value = 0;
            while (value < needle.length
                   && !needlematch(needle, a, value))
            {
                ++value;
            }
            this.skip[needle.length - a - 1] = value;
        }
    }

    ///
    Range beFound(Range haystack) scope
    {
        import std.algorithm.comparison : max;

        if (!needle.length) return haystack;
        if (needle.length > haystack.length) return haystack[$ .. $];
        /* Search: */
        immutable limit = haystack.length - needle.length;
        for (size_t hpos = 0; hpos <= limit; )
        {
            size_t npos = needle.length - 1;
            while (pred(needle[npos], haystack[npos+hpos]))
            {
                if (npos == 0) return haystack[hpos .. $];
                --npos;
            }
            hpos += max(skip[npos], cast(sizediff_t) npos - occurrence(haystack[npos+hpos]));
        }
        return haystack[$ .. $];
    }

    ///
    @property size_t length()
    {
        return needle.length;
    }

    ///
    alias opDollar = length;
}

/// Ditto
BoyerMooreFinder!(binaryFun!(pred), Range) boyerMooreFinder
(alias pred = "a == b", Range)
(Range needle)
if ((isRandomAccessRange!(Range) && hasSlicing!Range) || isSomeString!Range)
{
    return typeof(return)(needle);
}

///
@safe pure nothrow unittest
{
    auto bmFinder = boyerMooreFinder("TG");

    string r = "TAGTGCCTGA";
    // search for the first match in the haystack r
    r = bmFinder.beFound(r);
    assert(r == "TGCCTGA");

    // continue search in haystack
    r = bmFinder.beFound(r[2 .. $]);
    assert(r == "TGA");
}

/**
Returns the common prefix of two ranges.

Params:
    pred = The predicate to use in comparing elements for commonality. Defaults
        to equality `"a == b"`.

    r1 = A $(REF_ALTTEXT forward range, isForwardRange, std,range,primitives) of
        elements.

    r2 = An $(REF_ALTTEXT input range, isInputRange, std,range,primitives) of
        elements.

Returns:
A slice of `r1` which contains the characters that both ranges start with,
if the first argument is a string; otherwise, the same as the result of
`takeExactly(r1, n)`, where `n` is the number of elements in the common
prefix of both ranges.

See_Also:
    $(REF takeExactly, std,range)
 */
auto commonPrefix(alias pred = "a == b", R1, R2)(R1 r1, R2 r2)
if (isForwardRange!R1 && isInputRange!R2 &&
    !isNarrowString!R1 &&
    is(typeof(binaryFun!pred(r1.front, r2.front))))
{
    import std.algorithm.comparison : min;
    static if (isRandomAccessRange!R1 && isRandomAccessRange!R2 &&
               hasLength!R1 && hasLength!R2 &&
               hasSlicing!R1)
    {
        immutable limit = min(r1.length, r2.length);
        foreach (i; 0 .. limit)
        {
            if (!binaryFun!pred(r1[i], r2[i]))
            {
                return r1[0 .. i];
            }
        }
        return r1[0 .. limit];
    }
    else
    {
        import std.range : takeExactly;
        auto result = r1.save;
        size_t i = 0;
        for (;
             !r1.empty && !r2.empty && binaryFun!pred(r1.front, r2.front);
             ++i, r1.popFront(), r2.popFront())
        {}
        return takeExactly(result, i);
    }
}

///
@safe unittest
{
    assert(commonPrefix("hello, world", "hello, there") == "hello, ");
}

/// ditto
auto commonPrefix(alias pred, R1, R2)(R1 r1, R2 r2)
if (isNarrowString!R1 && isInputRange!R2 &&
    is(typeof(binaryFun!pred(r1.front, r2.front))))
{
    import std.utf : decode;

    auto result = r1.save;
    immutable len = r1.length;
    size_t i = 0;

    for (size_t j = 0; i < len && !r2.empty; r2.popFront(), i = j)
    {
        immutable f = decode(r1, j);
        if (!binaryFun!pred(f, r2.front))
            break;
    }

    return result[0 .. i];
}

/// ditto
auto commonPrefix(R1, R2)(R1 r1, R2 r2)
if (isNarrowString!R1 && isInputRange!R2 && !isNarrowString!R2 &&
    is(typeof(r1.front == r2.front)))
{
    return commonPrefix!"a == b"(r1, r2);
}

/// ditto
auto commonPrefix(R1, R2)(R1 r1, R2 r2)
if (isNarrowString!R1 && isNarrowString!R2)
{
    import std.algorithm.comparison : min;

    static if (ElementEncodingType!R1.sizeof == ElementEncodingType!R2.sizeof)
    {
        import std.utf : stride, UTFException;

        immutable limit = min(r1.length, r2.length);
        for (size_t i = 0; i < limit;)
        {
            immutable codeLen = stride(r1, i);
            size_t j = 0;

            for (; j < codeLen && i < limit; ++i, ++j)
            {
                if (r1[i] != r2[i])
                    return r1[0 .. i - j];
            }

            if (i == limit && j < codeLen)
                throw new UTFException("Invalid UTF-8 sequence", i);
        }
        return r1[0 .. limit];
    }
    else
        return commonPrefix!"a == b"(r1, r2);
}

@safe unittest
{
    import std.algorithm.comparison : equal;
    import std.algorithm.iteration : filter;
    import std.conv : to;
    import std.exception : assertThrown;
    import std.meta : AliasSeq;
    import std.range;
    import std.utf : UTFException;

    assert(commonPrefix([1, 2, 3], [1, 2, 3, 4, 5]) == [1, 2, 3]);
    assert(commonPrefix([1, 2, 3, 4, 5], [1, 2, 3]) == [1, 2, 3]);
    assert(commonPrefix([1, 2, 3, 4], [1, 2, 3, 4]) == [1, 2, 3, 4]);
    assert(commonPrefix([1, 2, 3], [7, 2, 3, 4, 5]).empty);
    assert(commonPrefix([7, 2, 3, 4, 5], [1, 2, 3]).empty);
    assert(commonPrefix([1, 2, 3], cast(int[]) null).empty);
    assert(commonPrefix(cast(int[]) null, [1, 2, 3]).empty);
    assert(commonPrefix(cast(int[]) null, cast(int[]) null).empty);

    static foreach (S; AliasSeq!(char[], const(char)[], string,
                          wchar[], const(wchar)[], wstring,
                          dchar[], const(dchar)[], dstring))
    {
        static foreach (T; AliasSeq!(string, wstring, dstring))
        {
            assert(commonPrefix(to!S(""), to!T("")).empty);
            assert(commonPrefix(to!S(""), to!T("hello")).empty);
            assert(commonPrefix(to!S("hello"), to!T("")).empty);
            assert(commonPrefix(to!S("hello, world"), to!T("hello, there")) == to!S("hello, "));
            assert(commonPrefix(to!S("hello, there"), to!T("hello, world")) == to!S("hello, "));
            assert(commonPrefix(to!S("hello, "), to!T("hello, world")) == to!S("hello, "));
            assert(commonPrefix(to!S("hello, world"), to!T("hello, ")) == to!S("hello, "));
            assert(commonPrefix(to!S("hello, world"), to!T("hello, world")) == to!S("hello, world"));

            //Bug# 8890
            assert(commonPrefix(to!S("Пиво"), to!T("Пони"))== to!S("П"));
            assert(commonPrefix(to!S("Пони"), to!T("Пиво"))== to!S("П"));
            assert(commonPrefix(to!S("Пиво"), to!T("Пиво"))== to!S("Пиво"));
            assert(commonPrefix(to!S("\U0010FFFF\U0010FFFB\U0010FFFE"),
                                to!T("\U0010FFFF\U0010FFFB\U0010FFFC")) == to!S("\U0010FFFF\U0010FFFB"));
            assert(commonPrefix(to!S("\U0010FFFF\U0010FFFB\U0010FFFC"),
                                to!T("\U0010FFFF\U0010FFFB\U0010FFFE")) == to!S("\U0010FFFF\U0010FFFB"));
            assert(commonPrefix!"a != b"(to!S("Пиво"), to!T("онво")) == to!S("Пи"));
            assert(commonPrefix!"a != b"(to!S("онво"), to!T("Пиво")) == to!S("он"));
        }

        static assert(is(typeof(commonPrefix(to!S("Пиво"), filter!"true"("Пони"))) == S));
        assert(equal(commonPrefix(to!S("Пиво"), filter!"true"("Пони")), to!S("П")));

        static assert(is(typeof(commonPrefix(filter!"true"("Пиво"), to!S("Пони"))) ==
                      typeof(takeExactly(filter!"true"("П"), 1))));
        assert(equal(commonPrefix(filter!"true"("Пиво"), to!S("Пони")), takeExactly(filter!"true"("П"), 1)));
    }

    assertThrown!UTFException(commonPrefix("\U0010FFFF\U0010FFFB", "\U0010FFFF\U0010FFFB"[0 .. $ - 1]));

    assert(commonPrefix("12345"d, [49, 50, 51, 60, 60]) == "123"d);
    assert(commonPrefix([49, 50, 51, 60, 60], "12345" ) == [49, 50, 51]);
    assert(commonPrefix([49, 50, 51, 60, 60], "12345"d) == [49, 50, 51]);

    assert(commonPrefix!"a == ('0' + b)"("12345" , [1, 2, 3, 9, 9]) == "123");
    assert(commonPrefix!"a == ('0' + b)"("12345"d, [1, 2, 3, 9, 9]) == "123"d);
    assert(commonPrefix!"('0' + a) == b"([1, 2, 3, 9, 9], "12345" ) == [1, 2, 3]);
    assert(commonPrefix!"('0' + a) == b"([1, 2, 3, 9, 9], "12345"d) == [1, 2, 3]);
}

// count
/**
The first version counts the number of elements `x` in `r` for
which `pred(x, value)` is `true`. `pred` defaults to
equality. Performs $(BIGOH haystack.length) evaluations of `pred`.

The second version returns the number of times `needle` occurs in
`haystack`. Throws an exception if `needle.empty`, as the _count
of the empty range in any range would be infinite. Overlapped counts
are not considered, for example `count("aaa", "aa")` is `1`, not
`2`.

The third version counts the elements for which `pred(x)` is $(D
true). Performs $(BIGOH haystack.length) evaluations of `pred`.

The fourth version counts the number of elements in a range. It is
an optimization for the third version: if the given range has the
`length` property the count is returned right away, otherwise
performs $(BIGOH haystack.length) to walk the range.

Note: Regardless of the overload, `count` will not accept
infinite ranges for `haystack`.

Params:
    pred = The predicate to evaluate.
    haystack = The range to _count.
    needle = The element or sub-range to _count in the `haystack`.

Returns:
    The number of positions in the `haystack` for which `pred` returned true.
*/
size_t count(alias pred = "a == b", Range, E)(Range haystack, E needle)
if (isInputRange!Range && !isInfinite!Range &&
    is(typeof(binaryFun!pred(haystack.front, needle)) : bool))
{
    bool pred2(ElementType!Range a) { return binaryFun!pred(a, needle); }
    return count!pred2(haystack);
}

///
@safe unittest
{
    import std.uni : toLower;

    // count elements in range
    int[] a = [ 1, 2, 4, 3, 2, 5, 3, 2, 4 ];
    assert(count(a) == 9);
    assert(count(a, 2) == 3);
    assert(count!("a > b")(a, 2) == 5);
    // count range in range
    assert(count("abcadfabf", "ab") == 2);
    assert(count("ababab", "abab") == 1);
    assert(count("ababab", "abx") == 0);
    // fuzzy count range in range
    assert(count!((a, b) => toLower(a) == toLower(b))("AbcAdFaBf", "ab") == 2);
    // count predicate in range
    assert(count!("a > 1")(a) == 8);
}

@safe unittest
{
    import std.conv : text;

    int[] a = [ 1, 2, 4, 3, 2, 5, 3, 2, 4 ];
    assert(count(a, 2) == 3, text(count(a, 2)));
    assert(count!("a > b")(a, 2) == 5, text(count!("a > b")(a, 2)));

    // check strings
    assert(count("日本語")  == 3);
    assert(count("日本語"w) == 3);
    assert(count("日本語"d) == 3);

    assert(count!("a == '日'")("日本語")  == 1);
    assert(count!("a == '本'")("日本語"w) == 1);
    assert(count!("a == '語'")("日本語"d) == 1);
}

@safe unittest
{
    string s = "This is a fofofof list";
    string sub = "fof";
    assert(count(s, sub) == 2);
}

/// Ditto
size_t count(alias pred = "a == b", R1, R2)(R1 haystack, R2 needle)
if (isForwardRange!R1 && !isInfinite!R1 &&
    isForwardRange!R2 &&
    is(typeof(binaryFun!pred(haystack.front, needle.front)) : bool))
{
    assert(!needle.empty, "Cannot count occurrences of an empty range");

    static if (isInfinite!R2)
    {
        //Note: This is the special case of looking for an infinite inside a finite...
        //"How many instances of the Fibonacci sequence can you count in [1, 2, 3]?" - "None."
        return 0;
    }
    else
    {
        size_t result;
        //Note: haystack is not saved, because findskip is designed to modify it
        for ( ; findSkip!pred(haystack, needle.save) ; ++result)
        {}
        return result;
    }
}

/// Ditto
size_t count(alias pred, R)(R haystack)
if (isInputRange!R && !isInfinite!R &&
    is(typeof(unaryFun!pred(haystack.front)) : bool))
{
    size_t result;
    alias T = ElementType!R; //For narrow strings forces dchar iteration
    foreach (T elem; haystack)
        if (unaryFun!pred(elem)) ++result;
    return result;
}

/// Ditto
size_t count(R)(R haystack)
if (isInputRange!R && !isInfinite!R)
{
    return walkLength(haystack);
}

@safe unittest
{
    int[] a = [ 1, 2, 4, 3, 2, 5, 3, 2, 4 ];
    assert(count!("a == 3")(a) == 2);
    assert(count("日本語") == 3);
}

// Issue 11253
@safe nothrow unittest
{
    assert([1, 2, 3].count([2, 3]) == 1);
}

/++
    Counts elements in the given
    $(REF_ALTTEXT forward range, isForwardRange, std,range,primitives)
    until the given predicate is true for one of the given `needles`.

    Params:
        pred = The predicate for determining when to stop counting.
        haystack = The
            $(REF_ALTTEXT input range, isInputRange, std,range,primitives) to be
            counted.
        needles = Either a single element, or a
            $(REF_ALTTEXT forward range, isForwardRange, std,range,primitives)
            of elements, to be evaluated in turn against each
            element in `haystack` under the given predicate.

    Returns: The number of elements which must be popped from the front of
    `haystack` before reaching an element for which
    `startsWith!pred(haystack, needles)` is `true`. If
    `startsWith!pred(haystack, needles)` is not `true` for any element in
    `haystack`, then `-1` is returned. If only `pred` is provided,
    `pred(haystack)` is tested for each element.

    See_Also: $(REF indexOf, std,string)
  +/
ptrdiff_t countUntil(alias pred = "a == b", R, Rs...)(R haystack, Rs needles)
if (isForwardRange!R
    && Rs.length > 0
    && isForwardRange!(Rs[0]) == isInputRange!(Rs[0])
    && is(typeof(startsWith!pred(haystack, needles[0])))
    && (Rs.length == 1
    || is(typeof(countUntil!pred(haystack, needles[1 .. $])))))
{
    typeof(return) result;

    static if (needles.length == 1)
    {
        static if (hasLength!R) //Note: Narrow strings don't have length.
        {
            //We delegate to find because find is very efficient.
            //We store the length of the haystack so we don't have to save it.
            auto len = haystack.length;
            auto r2 = find!pred(haystack, needles[0]);
            if (!r2.empty)
              return cast(typeof(return)) (len - r2.length);
        }
        else
        {
            import std.range : dropOne;

            if (needles[0].empty)
              return 0;

            //Default case, slower route doing startsWith iteration
            for ( ; !haystack.empty ; ++result )
            {
                //We compare the first elements of the ranges here before
                //forwarding to startsWith. This avoids making useless saves to
                //haystack/needle if they aren't even going to be mutated anyways.
                //It also cuts down on the amount of pops on haystack.
                if (binaryFun!pred(haystack.front, needles[0].front))
                {
                    //Here, we need to save the needle before popping it.
                    //haystack we pop in all paths, so we do that, and then save.
                    haystack.popFront();
                    if (startsWith!pred(haystack.save, needles[0].save.dropOne()))
                      return result;
                }
                else
                  haystack.popFront();
            }
        }
    }
    else
    {
        foreach (i, Ri; Rs)
        {
            static if (isForwardRange!Ri)
            {
                if (needles[i].empty)
                  return 0;
            }
        }
        Tuple!Rs t;
        foreach (i, Ri; Rs)
        {
            static if (!isForwardRange!Ri)
            {
                t[i] = needles[i];
            }
        }
        for (; !haystack.empty ; ++result, haystack.popFront())
        {
            foreach (i, Ri; Rs)
            {
                static if (isForwardRange!Ri)
                {
                    t[i] = needles[i].save;
                }
            }
            if (startsWith!pred(haystack.save, t.expand))
            {
                return result;
            }
        }
    }

    //Because of @@@8804@@@: Avoids both "unreachable code" or "no return statement"
    static if (isInfinite!R) assert(0);
    else return -1;
}

/// ditto
ptrdiff_t countUntil(alias pred = "a == b", R, N)(R haystack, N needle)
if (isInputRange!R &&
    is(typeof(binaryFun!pred(haystack.front, needle)) : bool))
{
    bool pred2(ElementType!R a) { return binaryFun!pred(a, needle); }
    return countUntil!pred2(haystack);
}

///
@safe unittest
{
    assert(countUntil("hello world", "world") == 6);
    assert(countUntil("hello world", 'r') == 8);
    assert(countUntil("hello world", "programming") == -1);
    assert(countUntil("日本語", "本語") == 1);
    assert(countUntil("日本語", '語')   == 2);
    assert(countUntil("日本語", "五") == -1);
    assert(countUntil("日本語", '五') == -1);
    assert(countUntil([0, 7, 12, 22, 9], [12, 22]) == 2);
    assert(countUntil([0, 7, 12, 22, 9], 9) == 4);
    assert(countUntil!"a > b"([0, 7, 12, 22, 9], 20) == 3);
}

@safe unittest
{
    import std.algorithm.iteration : filter;
    import std.internal.test.dummyrange;

    assert(countUntil("日本語", "") == 0);
    assert(countUntil("日本語"d, "") == 0);

    assert(countUntil("", "") == 0);
    assert(countUntil("".filter!"true"(), "") == 0);

    auto rf = [0, 20, 12, 22, 9].filter!"true"();
    assert(rf.countUntil!"a > b"((int[]).init) == 0);
    assert(rf.countUntil!"a > b"(20) == 3);
    assert(rf.countUntil!"a > b"([20, 8]) == 3);
    assert(rf.countUntil!"a > b"([20, 10]) == -1);
    assert(rf.countUntil!"a > b"([20, 8, 0]) == -1);

    auto r = new ReferenceForwardRange!int([0, 1, 2, 3, 4, 5, 6]);
    auto r2 = new ReferenceForwardRange!int([3, 4]);
    auto r3 = new ReferenceForwardRange!int([3, 5]);
    assert(r.save.countUntil(3)  == 3);
    assert(r.save.countUntil(r2) == 3);
    assert(r.save.countUntil(7)  == -1);
    assert(r.save.countUntil(r3) == -1);
}

@safe unittest
{
    assert(countUntil("hello world", "world", "asd") == 6);
    assert(countUntil("hello world", "world", "ello") == 1);
    assert(countUntil("hello world", "world", "") == 0);
    assert(countUntil("hello world", "world", 'l') == 2);
}

/// ditto
ptrdiff_t countUntil(alias pred, R)(R haystack)
if (isInputRange!R &&
    is(typeof(unaryFun!pred(haystack.front)) : bool))
{
    typeof(return) i;
    static if (isRandomAccessRange!R)
    {
        //Optimized RA implementation. Since we want to count *and* iterate at
        //the same time, it is more efficient this way.
        static if (hasLength!R)
        {
            immutable len = cast(typeof(return)) haystack.length;
            for ( ; i < len ; ++i )
                if (unaryFun!pred(haystack[i])) return i;
        }
        else //if (isInfinite!R)
        {
            for ( ;  ; ++i )
                if (unaryFun!pred(haystack[i])) return i;
        }
    }
    else static if (hasLength!R)
    {
        //For those odd ranges that have a length, but aren't RA.
        //It is faster to quick find, and then compare the lengths
        auto r2 = find!pred(haystack.save);
        if (!r2.empty) return cast(typeof(return)) (haystack.length - r2.length);
    }
    else //Everything else
    {
        alias T = ElementType!R; //For narrow strings forces dchar iteration
        foreach (T elem; haystack)
        {
            if (unaryFun!pred(elem)) return i;
            ++i;
        }
    }

    //Because of @@@8804@@@: Avoids both "unreachable code" or "no return statement"
    static if (isInfinite!R) assert(0);
    else return -1;
}

///
@safe unittest
{
    import std.ascii : isDigit;
    import std.uni : isWhite;

    assert(countUntil!(std.uni.isWhite)("hello world") == 5);
    assert(countUntil!(std.ascii.isDigit)("hello world") == -1);
    assert(countUntil!"a > 20"([0, 7, 12, 22, 9]) == 3);
}

@safe unittest
{
    import std.internal.test.dummyrange;

    // References
    {
        // input
        ReferenceInputRange!int r;
        r = new ReferenceInputRange!int([0, 1, 2, 3, 4, 5, 6]);
        assert(r.countUntil(3) == 3);
        r = new ReferenceInputRange!int([0, 1, 2, 3, 4, 5, 6]);
        assert(r.countUntil(7) == -1);
    }
    {
        // forward
        auto r = new ReferenceForwardRange!int([0, 1, 2, 3, 4, 5, 6]);
        assert(r.save.countUntil([3, 4]) == 3);
        assert(r.save.countUntil(3) == 3);
        assert(r.save.countUntil([3, 7]) == -1);
        assert(r.save.countUntil(7) == -1);
    }
    {
        // infinite forward
        auto r = new ReferenceInfiniteForwardRange!int(0);
        assert(r.save.countUntil([3, 4]) == 3);
        assert(r.save.countUntil(3) == 3);
    }
}

/**
Checks if the given range ends with (one of) the given needle(s).
The reciprocal of `startsWith`.

Params:
    pred = The predicate to use for comparing elements between the range and
        the needle(s).

    doesThisEnd = The
        $(REF_ALTTEXT bidirectional range, isBidirectionalRange, std,range,primitives)
        to check.

    withOneOfThese = The needles to check against, which may be single
        elements, or bidirectional ranges of elements.

    withThis = The single element to check.

Returns:
0 if the needle(s) do not occur at the end of the given range;
otherwise the position of the matching needle, that is, 1 if the range ends
with `withOneOfThese[0]`, 2 if it ends with `withOneOfThese[1]`, and so
on.

In the case when no needle parameters are given, return `true` iff back of
`doesThisStart` fulfils predicate `pred`.
*/
uint endsWith(alias pred = "a == b", Range, Needles...)(Range doesThisEnd, Needles withOneOfThese)
if (isBidirectionalRange!Range && Needles.length > 1 &&
    is(typeof(.endsWith!pred(doesThisEnd, withOneOfThese[0])) : bool) &&
    is(typeof(.endsWith!pred(doesThisEnd, withOneOfThese[1 .. $])) : uint))
{
    alias haystack = doesThisEnd;
    alias needles  = withOneOfThese;

    // Make one pass looking for empty ranges in needles
    foreach (i, Unused; Needles)
    {
        // Empty range matches everything
        static if (!is(typeof(binaryFun!pred(haystack.back, needles[i])) : bool))
        {
            if (needles[i].empty) return i + 1;
        }
    }

    for (; !haystack.empty; haystack.popBack())
    {
        foreach (i, Unused; Needles)
        {
            static if (is(typeof(binaryFun!pred(haystack.back, needles[i])) : bool))
            {
                // Single-element
                if (binaryFun!pred(haystack.back, needles[i]))
                {
                    // found, but continue to account for one-element
                    // range matches (consider endsWith("ab", "b",
                    // 'b') should return 1, not 2).
                    continue;
                }
            }
            else
            {
                if (binaryFun!pred(haystack.back, needles[i].back))
                    continue;
            }

            // This code executed on failure to match
            // Out with this guy, check for the others
            uint result = endsWith!pred(haystack, needles[0 .. i], needles[i + 1 .. $]);
            if (result > i) ++result;
            return result;
        }

        // If execution reaches this point, then the back matches for all
        // needles ranges. What we need to do now is to lop off the back of
        // all ranges involved and recurse.
        foreach (i, Unused; Needles)
        {
            static if (is(typeof(binaryFun!pred(haystack.back, needles[i])) : bool))
            {
                // Test has passed in the previous loop
                return i + 1;
            }
            else
            {
                needles[i].popBack();
                if (needles[i].empty) return i + 1;
            }
        }
    }
    return 0;
}

/// Ditto
bool endsWith(alias pred = "a == b", R1, R2)(R1 doesThisEnd, R2 withThis)
if (isBidirectionalRange!R1 &&
    isBidirectionalRange!R2 &&
    is(typeof(binaryFun!pred(doesThisEnd.back, withThis.back)) : bool))
{
    alias haystack = doesThisEnd;
    alias needle   = withThis;

    static if (is(typeof(pred) : string))
        enum isDefaultPred = pred == "a == b";
    else
        enum isDefaultPred = false;

    static if (isDefaultPred && isArray!R1 && isArray!R2 &&
               is(Unqual!(ElementEncodingType!R1) == Unqual!(ElementEncodingType!R2)))
    {
        if (haystack.length < needle.length) return false;

        return haystack[$ - needle.length .. $] == needle;
    }
    else
    {
        import std.range : retro;
        return startsWith!pred(retro(doesThisEnd), retro(withThis));
    }
}

/// Ditto
bool endsWith(alias pred = "a == b", R, E)(R doesThisEnd, E withThis)
if (isBidirectionalRange!R &&
    is(typeof(binaryFun!pred(doesThisEnd.back, withThis)) : bool))
{
    if (doesThisEnd.empty)
        return false;

    static if (is(typeof(pred) : string))
        enum isDefaultPred = pred == "a == b";
    else
        enum isDefaultPred = false;

    alias predFunc = binaryFun!pred;

    // auto-decoding special case
    static if (isNarrowString!R)
    {
        // statically determine decoding is unnecessary to evaluate pred
        static if (isDefaultPred && isSomeChar!E && E.sizeof <= ElementEncodingType!R.sizeof)
            return doesThisEnd[$ - 1] == withThis;
        // specialize for ASCII as to not change previous behavior
        else
        {
            if (withThis <= 0x7F)
                return predFunc(doesThisEnd[$ - 1], withThis);
            else
                return predFunc(doesThisEnd.back, withThis);
        }
    }
    else
    {
        return predFunc(doesThisEnd.back, withThis);
    }
}

/// Ditto
bool endsWith(alias pred, R)(R doesThisEnd)
if (isInputRange!R &&
    ifTestable!(typeof(doesThisEnd.front), unaryFun!pred))
{
    return !doesThisEnd.empty && unaryFun!pred(doesThisEnd.back);
}

///
@safe unittest
{
    import std.ascii : isAlpha;
    assert("abc".endsWith!(a => a.isAlpha));
    assert("abc".endsWith!isAlpha);

    assert(!"ab1".endsWith!(a => a.isAlpha));

    assert(!"ab1".endsWith!isAlpha);
    assert(!"".endsWith!(a => a.isAlpha));

    import std.algorithm.comparison : among;
    assert("abc".endsWith!(a => a.among('c', 'd') != 0));
    assert(!"abc".endsWith!(a => a.among('a', 'b') != 0));

    assert(endsWith("abc", ""));
    assert(!endsWith("abc", "b"));
    assert(endsWith("abc", "a", 'c') == 2);
    assert(endsWith("abc", "c", "a") == 1);
    assert(endsWith("abc", "c", "c") == 1);
    assert(endsWith("abc", "bc", "c") == 2);
    assert(endsWith("abc", "x", "c", "b") == 2);
    assert(endsWith("abc", "x", "aa", "bc") == 3);
    assert(endsWith("abc", "x", "aaa", "sab") == 0);
    assert(endsWith("abc", "x", "aaa", 'c', "sab") == 3);
}

@safe unittest
{
    import std.algorithm.iteration : filterBidirectional;
    import std.conv : to;
    import std.meta : AliasSeq;

    static foreach (S; AliasSeq!(char[], wchar[], dchar[], string, wstring, dstring))
    {
        assert(!endsWith(to!S("abc"), 'a'));
        assert(endsWith(to!S("abc"), 'a', 'c') == 2);
        assert(!endsWith(to!S("abc"), 'x', 'n', 'b'));
        assert(endsWith(to!S("abc"), 'x', 'n', 'c') == 3);
        assert(endsWith(to!S("abc\uFF28"), 'a', '\uFF28', 'c') == 2);

        static foreach (T; AliasSeq!(char[], wchar[], dchar[], string, wstring, dstring))
        {
            //Lots of strings
            assert(endsWith(to!S("abc"), to!T("")));
            assert(!endsWith(to!S("abc"), to!T("a")));
            assert(!endsWith(to!S("abc"), to!T("b")));
            assert(endsWith(to!S("abc"), to!T("bc"), 'c') == 2);
            assert(endsWith(to!S("abc"), to!T("a"), "c") == 2);
            assert(endsWith(to!S("abc"), to!T("c"), "a") == 1);
            assert(endsWith(to!S("abc"), to!T("c"), "c") == 1);
            assert(endsWith(to!S("abc"), to!T("x"), 'c', "b") == 2);
            assert(endsWith(to!S("abc"), 'x', to!T("aa"), "bc") == 3);
            assert(endsWith(to!S("abc"), to!T("x"), "aaa", "sab") == 0);
            assert(endsWith(to!S("abc"), to!T("x"), "aaa", "c", "sab") == 3);
            assert(endsWith(to!S("\uFF28el\uFF4co"), to!T("l\uFF4co")));
            assert(endsWith(to!S("\uFF28el\uFF4co"), to!T("lo"), to!T("l\uFF4co")) == 2);

            //Unicode
            assert(endsWith(to!S("\uFF28el\uFF4co"), to!T("l\uFF4co")));
            assert(endsWith(to!S("\uFF28el\uFF4co"), to!T("lo"), to!T("l\uFF4co")) == 2);
            assert(endsWith(to!S("日本語"), to!T("本語")));
            assert(endsWith(to!S("日本語"), to!T("日本語")));
            assert(!endsWith(to!S("本語"), to!T("日本語")));

            //Empty
            assert(endsWith(to!S(""),  T.init));
            assert(!endsWith(to!S(""), 'a'));
            assert(endsWith(to!S("a"), T.init));
            assert(endsWith(to!S("a"), T.init, "") == 1);
            assert(endsWith(to!S("a"), T.init, 'a') == 1);
            assert(endsWith(to!S("a"), 'a', T.init) == 2);
        }
    }

    static foreach (T; AliasSeq!(int, short))
    {{
        immutable arr = cast(T[])[0, 1, 2, 3, 4, 5];

        //RA range
        assert(endsWith(arr, cast(int[]) null));
        assert(!endsWith(arr, 0));
        assert(!endsWith(arr, 4));
        assert(endsWith(arr, 5));
        assert(endsWith(arr, 0, 4, 5) == 3);
        assert(endsWith(arr, [5]));
        assert(endsWith(arr, [4, 5]));
        assert(endsWith(arr, [4, 5], 7) == 1);
        assert(!endsWith(arr, [2, 4, 5]));
        assert(endsWith(arr, [2, 4, 5], [3, 4, 5]) == 2);

        //Normal input range
        assert(!endsWith(filterBidirectional!"true"(arr), 4));
        assert(endsWith(filterBidirectional!"true"(arr), 5));
        assert(endsWith(filterBidirectional!"true"(arr), [5]));
        assert(endsWith(filterBidirectional!"true"(arr), [4, 5]));
        assert(endsWith(filterBidirectional!"true"(arr), [4, 5], 7) == 1);
        assert(!endsWith(filterBidirectional!"true"(arr), [2, 4, 5]));
        assert(endsWith(filterBidirectional!"true"(arr), [2, 4, 5], [3, 4, 5]) == 2);
        assert(endsWith(arr, filterBidirectional!"true"([4, 5])));
        assert(endsWith(arr, filterBidirectional!"true"([4, 5]), 7) == 1);
        assert(!endsWith(arr, filterBidirectional!"true"([2, 4, 5])));
        assert(endsWith(arr, [2, 4, 5], filterBidirectional!"true"([3, 4, 5])) == 2);

        //Non-default pred
        assert(endsWith!("a%10 == b%10")(arr, [14, 15]));
        assert(!endsWith!("a%10 == b%10")(arr, [15, 14]));
    }}
}

// Rebindable doesn't work with structs
// see: https://github.com/dlang/phobos/pull/6136
private template RebindableOrUnqual(T)
{
    static if (is(T == class) || is(T == interface) || isDynamicArray!T || isAssociativeArray!T)
        alias RebindableOrUnqual = Rebindable!T;
    else
        alias RebindableOrUnqual = Unqual!T;
}

/**
Iterates the passed range and selects the extreme element with `less`.
If the extreme element occurs multiple time, the first occurrence will be
returned.

Params:
    map = custom accessor for the comparison key
    selector = custom mapping for the extrema selection
    seed = custom seed to use as initial element
    r = Range from which the extreme value will be selected

Returns:
    The extreme value according to `map` and `selector` of the passed-in values.
*/
private auto extremum(alias map, alias selector = "a < b", Range)(Range r)
if (isInputRange!Range && !isInfinite!Range &&
    is(typeof(unaryFun!map(ElementType!(Range).init))))
in
{
    assert(!r.empty, "r is an empty range");
}
do
{
    alias Element = ElementType!Range;
    RebindableOrUnqual!Element seed = r.front;
    r.popFront();
    return extremum!(map, selector)(r, seed);
}

private auto extremum(alias map, alias selector = "a < b", Range,
                      RangeElementType = ElementType!Range)
                     (Range r, RangeElementType seedElement)
if (isInputRange!Range && !isInfinite!Range &&
    !is(CommonType!(ElementType!Range, RangeElementType) == void) &&
     is(typeof(unaryFun!map(ElementType!(Range).init))))
{
    alias mapFun = unaryFun!map;
    alias selectorFun = binaryFun!selector;

    alias Element = ElementType!Range;
    alias CommonElement = CommonType!(Element, RangeElementType);
    RebindableOrUnqual!CommonElement extremeElement = seedElement;


    // if we only have one statement in the loop, it can be optimized a lot better
    static if (__traits(isSame, map, a => a))
    {

        // direct access via a random access range is faster
        static if (isRandomAccessRange!Range)
        {
            foreach (const i; 0 .. r.length)
            {
                if (selectorFun(r[i], extremeElement))
                {
                    extremeElement = r[i];
                }
            }
        }
        else
        {
            while (!r.empty)
            {
                if (selectorFun(r.front, extremeElement))
                {
                    extremeElement = r.front;
                }
                r.popFront();
            }
        }
    }
    else
    {
        alias MapType = Unqual!(typeof(mapFun(CommonElement.init)));
        MapType extremeElementMapped = mapFun(extremeElement);

        // direct access via a random access range is faster
        static if (isRandomAccessRange!Range)
        {
            foreach (const i; 0 .. r.length)
            {
                MapType mapElement = mapFun(r[i]);
                if (selectorFun(mapElement, extremeElementMapped))
                {
                    extremeElement = r[i];
                    extremeElementMapped = mapElement;
                }
            }
        }
        else
        {
            while (!r.empty)
            {
                MapType mapElement = mapFun(r.front);
                if (selectorFun(mapElement, extremeElementMapped))
                {
                    extremeElement = r.front;
                    extremeElementMapped = mapElement;
                }
                r.popFront();
            }
        }
    }
    return extremeElement;
}

private auto extremum(alias selector = "a < b", Range)(Range r)
if (isInputRange!Range && !isInfinite!Range &&
    !is(typeof(unaryFun!selector(ElementType!(Range).init))))
{
    return extremum!(a => a, selector)(r);
}

// if we only have one statement in the loop it can be optimized a lot better
private auto extremum(alias selector = "a < b", Range,
                      RangeElementType = ElementType!Range)
                     (Range r, RangeElementType seedElement)
if (isInputRange!Range && !isInfinite!Range &&
    !is(CommonType!(ElementType!Range, RangeElementType) == void) &&
    !is(typeof(unaryFun!selector(ElementType!(Range).init))))
{
    return extremum!(a => a, selector)(r, seedElement);
}

@safe pure unittest
{
    // allows a custom map to select the extremum
    assert([[0, 4], [1, 2]].extremum!"a[0]" == [0, 4]);
    assert([[0, 4], [1, 2]].extremum!"a[1]" == [1, 2]);

    // allows a custom selector for comparison
    assert([[0, 4], [1, 2]].extremum!("a[0]", "a > b") == [1, 2]);
    assert([[0, 4], [1, 2]].extremum!("a[1]", "a > b") == [0, 4]);

    // use a custom comparator
    import std.math : cmp;
    assert([-2., 0, 5].extremum!cmp == 5.0);
    assert([-2., 0, 2].extremum!`cmp(a, b) < 0` == -2.0);

    // combine with map
    import std.range : enumerate;
    assert([-3., 0, 5].enumerate.extremum!(`a.value`, cmp) == tuple(2, 5.0));
    assert([-2., 0, 2].enumerate.extremum!(`a.value`, `cmp(a, b) < 0`) == tuple(0, -2.0));

    // seed with a custom value
    int[] arr;
    assert(arr.extremum(1) == 1);
}

@safe pure nothrow unittest
{
    // 2d seeds
    int[][] arr2d;
    assert(arr2d.extremum([1]) == [1]);

    // allow seeds of different types (implicit casting)
    assert(extremum([2, 3, 4], 1.5) == 1.5);
}

@safe pure unittest
{
    import std.range : enumerate, iota;

    // forward ranges
    assert(iota(1, 5).extremum() == 1);
    assert(iota(2, 5).enumerate.extremum!"a.value" == tuple(0, 2));

    // should work with const
    const(int)[] immArr = [2, 1, 3];
    assert(immArr.extremum == 1);

    // should work with immutable
    immutable(int)[] immArr2 = [2, 1, 3];
    assert(immArr2.extremum == 1);

    // with strings
    assert(["b", "a", "c"].extremum == "a");

    // with all dummy ranges
    import std.internal.test.dummyrange;
    foreach (DummyType; AllDummyRanges)
    {
        DummyType d;
        assert(d.extremum == 1);
        assert(d.extremum!(a => a)  == 1);
        assert(d.extremum!`a > b` == 10);
        assert(d.extremum!(a => a, `a > b`) == 10);
    }
}

@nogc @safe nothrow pure unittest
{
    static immutable arr = [7, 3, 4, 2, 1, 8];
    assert(arr.extremum == 1);

    static immutable arr2d = [[1, 9], [3, 1], [4, 2]];
    assert(arr2d.extremum!"a[1]" == arr2d[1]);
}

// https://issues.dlang.org/show_bug.cgi?id=17982
@safe unittest
{
    class B
    {
        int val;
        this(int val){ this.val = val; }
    }

    const(B) doStuff(const(B)[] v)
    {
        return v.extremum!"a.val";
    }
    assert(doStuff([new B(1), new B(0), new B(2)]).val == 0);

    const(B)[] arr = [new B(0), new B(1)];
    // can't compare directly - https://issues.dlang.org/show_bug.cgi?id=1824
    assert(arr.extremum!"a.val".val == 0);
}

// find
/**
Finds an individual element in an $(REF_ALTTEXT input range, isInputRange, std,range,primitives).
Elements of `haystack` are compared with `needle` by using predicate
`pred` with `pred(haystack.front, needle)`.
`find` performs $(BIGOH walkLength(haystack)) evaluations of `pred`.

The predicate is passed to $(REF binaryFun, std, functional), and can either accept a
string, or any callable that can be executed via `pred(element, element)`.

To _find the last occurrence of `needle` in a
$(REF_ALTTEXT bidirectional, isBidirectionalRange, std,range,primitives) `haystack`,
call `find(retro(haystack), needle)`. See $(REF retro, std,range).

If no `needle` is provided, `pred(haystack.front)` will be evaluated on each
element of the input range.

If `input` is a $(REF_ALTTEXT forward range, isForwardRange, std,range,primitives),
`needle` can be a $(REF_ALTTEXT forward range, isForwardRange, std,range,primitives) too.
In this case `startsWith!pred(haystack, needle)` is evaluated on each evaluation.

Note:
    `find` behaves similar to `dropWhile` in other languages.

Complexity:
    `find` performs $(BIGOH walkLength(haystack)) evaluations of `pred`.
    There are specializations that improve performance by taking
    advantage of $(REF_ALTTEXT bidirectional, isBidirectionalRange, std,range,primitives)
    or $(REF_ALTTEXT random access, isRandomAccess, std,range,primitives)
    ranges (where possible).

Params:

    pred = The predicate for comparing each element with the needle, defaulting to equality `"a == b"`.
           The negated predicate `"a != b"` can be used to search instead for the first
           element $(I not) matching the needle.

    haystack = The $(REF_ALTTEXT input range, isInputRange, std,range,primitives)
               searched in.

    needle = The element searched for.

Returns:

    `haystack` advanced such that the front element is the one searched for;
    that is, until `binaryFun!pred(haystack.front, needle)` is `true`. If no
    such position exists, returns an empty `haystack`.

See_ALso: $(LREF findAdjacent), $(LREF findAmong), $(LREF findSkip), $(LREF findSplit), $(LREF startsWith)
*/
InputRange find(alias pred = "a == b", InputRange, Element)(InputRange haystack, scope Element needle)
if (isInputRange!InputRange &&
    is (typeof(binaryFun!pred(haystack.front, needle)) : bool))
{
    alias R = InputRange;
    alias E = Element;
    alias predFun = binaryFun!pred;
    static if (is(typeof(pred == "a == b")))
        enum isDefaultPred = pred == "a == b";
    else
        enum isDefaultPred = false;
    enum  isIntegralNeedle = isSomeChar!E || isIntegral!E || isBoolean!E;

    alias EType  = ElementType!R;

    // If the haystack is a SortedRange we can use binary search to find the needle.
    // Works only for the default find predicate and any SortedRange predicate.
    // 8829 enhancement
    import std.range : SortedRange;
    static if (is(InputRange : SortedRange!TT, TT) && isDefaultPred)
    {
        auto lb = haystack.lowerBound(needle);
        if (lb.length == haystack.length || haystack[lb.length] != needle)
            return haystack[$ .. $];

        return haystack[lb.length .. $];
    }
    else static if (isNarrowString!R)
    {
        alias EEType = ElementEncodingType!R;
        alias UEEType = Unqual!EEType;

        //These are two special cases which can search without decoding the UTF stream.
        static if (isDefaultPred && isIntegralNeedle)
        {
            import std.utf : canSearchInCodeUnits;

            //This special case deals with UTF8 search, when the needle
            //is represented by a single code point.
            //Note: "needle <= 0x7F" properly handles sign via unsigned promotion
            static if (is(UEEType == char))
            {
                if (!__ctfe && canSearchInCodeUnits!char(needle))
                {
                    static R trustedMemchr(ref R haystack, ref E needle) @trusted nothrow pure
                    {
                        import core.stdc.string : memchr;
                        auto ptr = memchr(haystack.ptr, needle, haystack.length);
                        return ptr ?
                             haystack[cast(char*) ptr - haystack.ptr .. $] :
                             haystack[$ .. $];
                    }
                    return trustedMemchr(haystack, needle);
                }
            }

            //Ditto, but for UTF16
            static if (is(UEEType == wchar))
            {
                if (canSearchInCodeUnits!wchar(needle))
                {
                    foreach (i, ref EEType e; haystack)
                    {
                        if (e == needle)
                            return haystack[i .. $];
                    }
                    return haystack[$ .. $];
                }
            }
        }

        //Previous conditional optimizations did not succeed. Fallback to
        //unconditional implementations
        static if (isDefaultPred)
        {
            import std.utf : encode;

            //In case of default pred, it is faster to do string/string search.
            UEEType[is(UEEType == char) ? 4 : 2] buf;

            size_t len = encode(buf, needle);
            return find(haystack, buf[0 .. len]);
        }
        else
        {
            import std.utf : decode;

            //Explicit pred: we must test each character by the book.
            //We choose a manual decoding approach, because it is faster than
            //the built-in foreach, or doing a front/popFront for-loop.
            immutable len = haystack.length;
            size_t i = 0, next = 0;
            while (next < len)
            {
                if (predFun(decode(haystack, next), needle))
                    return haystack[i .. $];
                i = next;
            }
            return haystack[$ .. $];
        }
    }
    else static if (isArray!R)
    {
        //10403 optimization
        static if (isDefaultPred && isIntegral!EType && EType.sizeof == 1 && isIntegralNeedle)
        {
            import std.algorithm.comparison : max, min;

            R findHelper(ref R haystack, ref E needle) @trusted nothrow pure
            {
                import core.stdc.string : memchr;

                EType* ptr = null;
                //Note: we use "min/max" to handle sign mismatch.
                if (min(EType.min, needle) == EType.min &&
                    max(EType.max, needle) == EType.max)
                {
                    ptr = cast(EType*) memchr(haystack.ptr, needle,
                        haystack.length);
                }

                return ptr ?
                    haystack[ptr - haystack.ptr .. $] :
                    haystack[$ .. $];
            }

            if (!__ctfe)
                return findHelper(haystack, needle);
        }

        //Default implementation.
        foreach (i, ref e; haystack)
            if (predFun(e, needle))
                return haystack[i .. $];
        return haystack[$ .. $];
    }
    else
    {
        //Everything else. Walk.
        for ( ; !haystack.empty; haystack.popFront() )
        {
            if (predFun(haystack.front, needle))
                break;
        }
        return haystack;
    }
}

///
@safe unittest
{
    import std.range.primitives;

    auto arr = [1, 2, 4, 4, 4, 4, 5, 6, 9];
    assert(arr.find(4) == [4, 4, 4, 4, 5, 6, 9]);
    assert(arr.find(1) == arr);
    assert(arr.find(9) == [9]);
    assert(arr.find!((a, b) => a > b)(4) == [5, 6, 9]);
    assert(arr.find!((a, b) => a < b)(4) == arr);
    assert(arr.find(0).empty);
    assert(arr.find(10).empty);
    assert(arr.find(8).empty);

    assert(find("hello, world", ',') == ", world");
}

/// Case-insensitive find of a string
@safe unittest
{
    import std.range.primitives;
    import std.uni : toLower;

    string[] s = ["Hello", "world", "!"];
    assert(s.find!((a, b) => toLower(a) == b)("hello") == s);
}

@safe unittest
{
    import std.algorithm.comparison : equal;
    import std.container : SList;

    auto lst = SList!int(1, 2, 5, 7, 3);
    assert(lst.front == 1);
    auto r = find(lst[], 5);
    assert(equal(r, SList!int(5, 7, 3)[]));
    assert(find([1, 2, 3, 5], 4).empty);
    assert(equal(find!"a > b"("hello", 'k'), "llo"));
}

@safe pure nothrow unittest
{
    assert(!find              ([1, 2, 3], 2).empty);
    assert(!find!((a,b)=>a == b)([1, 2, 3], 2).empty);
    assert(!find              ([1, 2, 3], 2).empty);
    assert(!find!((a,b)=>a == b)([1, 2, 3], 2).empty);
}

@safe pure unittest
{
    import std.meta : AliasSeq;
    static foreach (R; AliasSeq!(string, wstring, dstring))
    {
        static foreach (E; AliasSeq!(char, wchar, dchar))
        {
            assert(find              ("hello world", 'w') == "world");
            assert(find!((a,b)=>a == b)("hello world", 'w') == "world");
            assert(find              ("日c語", 'c') == "c語");
            assert(find!((a,b)=>a == b)("日c語", 'c') == "c語");
            assert(find              ("0123456789", 'A').empty);
            static if (E.sizeof >= 2)
            {
                assert(find              ("日本語", '本') == "本語");
                assert(find!((a,b)=>a == b)("日本語", '本') == "本語");
            }
        }
    }
}

@safe unittest
{
    //CTFE
    static assert(find("abc", 'b') == "bc");
    static assert(find("日b語", 'b') == "b語");
    static assert(find("日本語", '本') == "本語");
    static assert(find([1, 2, 3], 2)  == [2, 3]);

    static assert(find              ([1, 2, 3], 2));
    static assert(find!((a,b)=>a == b)([1, 2, 3], 2));
    static assert(find              ([1, 2, 3], 2));
    static assert(find!((a,b)=>a == b)([1, 2, 3], 2));
}

@safe unittest
{
    import std.exception : assertCTFEable;
    import std.meta : AliasSeq;

    void dg() @safe pure nothrow
    {
        byte[]  sarr = [1, 2, 3, 4];
        ubyte[] uarr = [1, 2, 3, 4];
        static foreach (arr; AliasSeq!(sarr, uarr))
        {
            static foreach (T; AliasSeq!(byte, ubyte, int, uint))
            {
                assert(find(arr, cast(T) 3) == arr[2 .. $]);
                assert(find(arr, cast(T) 9) == arr[$ .. $]);
            }
            assert(find(arr, 256) == arr[$ .. $]);
        }
    }
    dg();
    assertCTFEable!dg;
}

@safe unittest
{
    // Bugzilla 11603
    enum Foo : ubyte { A }
    assert([Foo.A].find(Foo.A).empty == false);

    ubyte x = 0;
    assert([x].find(x).empty == false);
}

/// ditto
InputRange find(alias pred, InputRange)(InputRange haystack)
if (isInputRange!InputRange)
{
    alias R = InputRange;
    alias predFun = unaryFun!pred;
    static if (isNarrowString!R)
    {
        import std.utf : decode;

        immutable len = haystack.length;
        size_t i = 0, next = 0;
        while (next < len)
        {
            if (predFun(decode(haystack, next)))
                return haystack[i .. $];
            i = next;
        }
        return haystack[$ .. $];
    }
    else
    {
        //standard range
        for ( ; !haystack.empty; haystack.popFront() )
        {
            if (predFun(haystack.front))
                break;
        }
        return haystack;
    }
}

///
@safe unittest
{
    auto arr = [ 1, 2, 3, 4, 1 ];
    assert(find!("a > 2")(arr) == [ 3, 4, 1 ]);

    // with predicate alias
    bool pred(int x) { return x + 1 > 1.5; }
    assert(find!(pred)(arr) == arr);
}

@safe pure unittest
{
    int[] r = [ 1, 2, 3 ];
    assert(find!(a=>a > 2)(r) == [3]);
    bool pred(int x) { return x + 1 > 1.5; }
    assert(find!(pred)(r) == r);

    assert(find!(a=>a > 'v')("hello world") == "world");
    assert(find!(a=>a%4 == 0)("日本語") == "本語");
}

/// ditto
R1 find(alias pred = "a == b", R1, R2)(R1 haystack, scope R2 needle)
if (isForwardRange!R1 && isForwardRange!R2
        && is(typeof(binaryFun!pred(haystack.front, needle.front)) : bool))
{
    static if (!isRandomAccessRange!R1)
    {
        static if (is(typeof(pred == "a == b")) && pred == "a == b" && isSomeString!R1 && isSomeString!R2
                && haystack[0].sizeof == needle[0].sizeof)
        {
            // return cast(R1) find(representation(haystack), representation(needle));
            // Specialization for simple string search
            alias Representation =
                Select!(haystack[0].sizeof == 1, ubyte[],
                    Select!(haystack[0].sizeof == 2, ushort[], uint[]));
            // Will use the array specialization
            static TO force(TO, T)(inout T r) @trusted { return cast(TO) r; }
            return force!R1(.find!(pred, Representation, Representation)
                (force!Representation(haystack), force!Representation(needle)));
        }
        else
        {
            return simpleMindedFind!pred(haystack, needle);
        }
    }
    else static if (!isBidirectionalRange!R2 || !hasSlicing!R1)
    {
        static if (!is(ElementType!R1 == ElementType!R2))
        {
            return simpleMindedFind!pred(haystack, needle);
        }
        else
        {
            // Prepare the search with needle's first element
            if (needle.empty)
                return haystack;

            haystack = .find!pred(haystack, needle.front);

            static if (hasLength!R1 && hasLength!R2 && is(typeof(takeNone(haystack)) == R1))
            {
                if (needle.length > haystack.length)
                    return takeNone(haystack);
            }
            else
            {
                if (haystack.empty)
                    return haystack;
            }

            needle.popFront();
            size_t matchLen = 1;

            // Loop invariant: haystack[0 .. matchLen] matches everything in
            // the initial needle that was popped out of needle.
            for (;;)
            {
                // Extend matchLength as much as possible
                for (;;)
                {
                    import std.range : takeNone;

                    if (needle.empty || haystack.empty)
                        return haystack;

                    static if (hasLength!R1 && is(typeof(takeNone(haystack)) == R1))
                    {
                        if (matchLen == haystack.length)
                            return takeNone(haystack);
                    }

                    if (!binaryFun!pred(haystack[matchLen], needle.front))
                        break;

                    ++matchLen;
                    needle.popFront();
                }

                auto bestMatch = haystack[0 .. matchLen];
                haystack.popFront();
                haystack = .find!pred(haystack, bestMatch);
            }
        }
    }
    else // static if (hasSlicing!R1 && isBidirectionalRange!R2)
    {
        if (needle.empty) return haystack;

        static if (hasLength!R2)
        {
            immutable needleLength = needle.length;
        }
        else
        {
            immutable needleLength = walkLength(needle.save);
        }
        if (needleLength > haystack.length)
        {
            return haystack[haystack.length .. haystack.length];
        }
        // Optimization in case the ranges are both SortedRanges.
        // Binary search can be used to find the first occurence
        // of the first element of the needle in haystack.
        // When it is found O(walklength(needle)) steps are performed.
        // 8829 enhancement
        import std.algorithm.comparison : mismatch;
        import std.range : SortedRange;
        static if (is(R1 == R2)
                && is(R1 : SortedRange!TT, TT)
                && pred == "a == b")
        {
            auto needleFirstElem = needle[0];
            auto partitions      = haystack.trisect(needleFirstElem);
            auto firstElemLen    = partitions[1].length;
            size_t count         = 0;

            if (firstElemLen == 0)
                return haystack[$ .. $];

            while (needle.front() == needleFirstElem)
            {
                needle.popFront();
                ++count;

                if (count > firstElemLen)
                    return haystack[$ .. $];
            }

            auto m = mismatch(partitions[2], needle);

            if (m[1].empty)
                return haystack[partitions[0].length + partitions[1].length - count .. $];
        }
        else static if (isRandomAccessRange!R2)
        {
            immutable lastIndex = needleLength - 1;
            auto last = needle[lastIndex];
            size_t j = lastIndex, skip = 0;
            for (; j < haystack.length;)
            {
                if (!binaryFun!pred(haystack[j], last))
                {
                    ++j;
                    continue;
                }
                immutable k = j - lastIndex;
                // last elements match
                for (size_t i = 0;; ++i)
                {
                    if (i == lastIndex)
                        return haystack[k .. haystack.length];
                    if (!binaryFun!pred(haystack[k + i], needle[i]))
                        break;
                }
                if (skip == 0)
                {
                    skip = 1;
                    while (skip < needleLength && needle[needleLength - 1 - skip] != needle[needleLength - 1])
                    {
                        ++skip;
                    }
                }
                j += skip;
            }
        }
        else
        {
            // @@@BUG@@@
            // auto needleBack = moveBack(needle);
            // Stage 1: find the step
            size_t step = 1;
            auto needleBack = needle.back;
            needle.popBack();
            for (auto i = needle.save; !i.empty && i.back != needleBack;
                    i.popBack(), ++step)
            {
            }
            // Stage 2: linear find
            size_t scout = needleLength - 1;
            for (;;)
            {
                if (scout >= haystack.length)
                    break;
                if (!binaryFun!pred(haystack[scout], needleBack))
                {
                    ++scout;
                    continue;
                }
                // Found a match with the last element in the needle
                auto cand = haystack[scout + 1 - needleLength .. haystack.length];
                if (startsWith!pred(cand, needle))
                {
                    // found
                    return cand;
                }
                scout += step;
            }
        }
        return haystack[haystack.length .. haystack.length];
    }
}

///
@safe unittest
{
    import std.container : SList;
    import std.range.primitives : empty;
    import std.typecons : Tuple;

    assert(find("hello, world", "World").empty);
    assert(find("hello, world", "wo") == "world");
    assert([1, 2, 3, 4].find(SList!int(2, 3)[]) == [2, 3, 4]);
    alias C = Tuple!(int, "x", int, "y");
    auto a = [C(1,0), C(2,0), C(3,1), C(4,0)];
    assert(a.find!"a.x == b"([2, 3]) == [C(2,0), C(3,1), C(4,0)]);
    assert(a[1 .. $].find!"a.x == b"([2, 3]) == [C(2,0), C(3,1), C(4,0)]);
}

@safe unittest
{
    import std.container : SList;
    alias C = Tuple!(int, "x", int, "y");
    assert([C(1,0), C(2,0), C(3,1), C(4,0)].find!"a.x == b"(SList!int(2, 3)[]) == [C(2,0), C(3,1), C(4,0)]);
}

@safe unittest // issue 12470
{
    import std.array : replace;
    inout(char)[] sanitize(inout(char)[] p)
    {
        return p.replace("\0", " ");
    }
    assert(sanitize("O\x00o") == "O o");
}

@safe unittest
{
    import std.algorithm.comparison : equal;
    import std.container : SList;

    auto lst = SList!int(1, 2, 5, 7, 3);
    static assert(isForwardRange!(int[]));
    static assert(isForwardRange!(typeof(lst[])));
    auto r = find(lst[], [2, 5]);
    assert(equal(r, SList!int(2, 5, 7, 3)[]));
}

@safe unittest
{
    import std.range : assumeSorted;

    auto r1 = assumeSorted([1, 2, 3, 3, 3, 4, 5, 6, 7, 8, 8, 8, 10]);
    auto r2 = assumeSorted([3, 3, 4, 5, 6, 7, 8, 8]);
    auto r3 = assumeSorted([3, 4, 5, 6, 7, 8]);
    auto r4 = assumeSorted([4, 5, 6]);
    auto r5 = assumeSorted([12, 13]);
    auto r6 = assumeSorted([8, 8, 10, 11]);
    auto r7 = assumeSorted([3, 3, 3, 3, 3, 3, 3]);

    assert(find(r1, r2) == assumeSorted([3, 3, 4, 5, 6, 7, 8, 8, 8, 10]));
    assert(find(r1, r3) == assumeSorted([3, 4, 5, 6, 7, 8, 8, 8, 10]));
    assert(find(r1, r4) == assumeSorted([4, 5, 6, 7, 8, 8, 8, 10]));
    assert(find(r1, r5).empty());
    assert(find(r1, r6).empty());
    assert(find(r1, r7).empty());
}

@safe unittest
{
    import std.algorithm.comparison : equal;
    // @@@BUG@@@ removing static below makes unittest fail
    static struct BiRange
    {
        int[] payload;
        @property bool empty() { return payload.empty; }
        @property BiRange save() { return this; }
        @property ref int front() { return payload[0]; }
        @property ref int back() { return payload[$ - 1]; }
        void popFront() { return payload.popFront(); }
        void popBack() { return payload.popBack(); }
    }
    auto r = BiRange([1, 2, 3, 10, 11, 4]);
    assert(equal(find(r, [10, 11]), [10, 11, 4]));
}

@safe unittest
{
    import std.container : SList;

    assert(find([ 1, 2, 3 ], SList!int(2, 3)[]) == [ 2, 3 ]);
    assert(find([ 1, 2, 1, 2, 3, 3 ], SList!int(2, 3)[]) == [ 2, 3, 3 ]);
}

//Bug# 8334
@safe unittest
{
    import std.algorithm.iteration : filter;
    import std.range;

    auto haystack = [1, 2, 3, 4, 1, 9, 12, 42];
    auto needle = [12, 42, 27];

    //different overload of find, but it's the base case.
    assert(find(haystack, needle).empty);

    assert(find(haystack, takeExactly(filter!"true"(needle), 3)).empty);
    assert(find(haystack, filter!"true"(needle)).empty);
}

// Internally used by some find() overloads above
private R1 simpleMindedFind(alias pred, R1, R2)(R1 haystack, scope R2 needle)
{
    enum estimateNeedleLength = hasLength!R1 && !hasLength!R2;

    static if (hasLength!R1)
    {
        static if (!hasLength!R2)
            size_t estimatedNeedleLength = 0;
        else
            immutable size_t estimatedNeedleLength = needle.length;
    }

    bool haystackTooShort()
    {
        static if (estimateNeedleLength)
        {
            return haystack.length < estimatedNeedleLength;
        }
        else
        {
            return haystack.empty;
        }
    }

  searching:
    for (;; haystack.popFront())
    {
        if (haystackTooShort())
        {
            // Failed search
            static if (hasLength!R1)
            {
                static if (is(typeof(haystack[haystack.length ..
                                                haystack.length]) : R1))
                    return haystack[haystack.length .. haystack.length];
                else
                    return R1.init;
            }
            else
            {
                assert(haystack.empty);
                return haystack;
            }
        }
        static if (estimateNeedleLength)
            size_t matchLength = 0;
        for (auto h = haystack.save, n = needle.save;
             !n.empty;
             h.popFront(), n.popFront())
        {
            if (h.empty || !binaryFun!pred(h.front, n.front))
            {
                // Failed searching n in h
                static if (estimateNeedleLength)
                {
                    if (estimatedNeedleLength < matchLength)
                        estimatedNeedleLength = matchLength;
                }
                continue searching;
            }
            static if (estimateNeedleLength)
                ++matchLength;
        }
        break;
    }
    return haystack;
}

@safe unittest
{
    // Test simpleMindedFind for the case where both haystack and needle have
    // length.
    struct CustomString
    {
    @safe:
        string _impl;

        // This is what triggers issue 7992.
        @property size_t length() const { return _impl.length; }
        @property void length(size_t len) { _impl.length = len; }

        // This is for conformance to the forward range API (we deliberately
        // make it non-random access so that we will end up in
        // simpleMindedFind).
        @property bool empty() const { return _impl.empty; }
        @property dchar front() const { return _impl.front; }
        void popFront() { _impl.popFront(); }
        @property CustomString save() { return this; }
    }

    // If issue 7992 occurs, this will throw an exception from calling
    // popFront() on an empty range.
    auto r = find(CustomString("a"), CustomString("b"));
    assert(r.empty);
}

/**
Finds two or more `needles` into a `haystack`. The predicate $(D
pred) is used throughout to compare elements. By default, elements are
compared for equality.

Params:

pred = The predicate to use for comparing elements.

haystack = The target of the search. Must be an input range.
If any of `needles` is a range with elements comparable to
elements in `haystack`, then `haystack` must be a
$(REF_ALTTEXT forward range, isForwardRange, std,range,primitives)
such that the search can backtrack.

needles = One or more items to search for. Each of `needles` must
be either comparable to one element in `haystack`, or be itself a
forward range with elements comparable with elements in
`haystack`.

Returns:

A tuple containing `haystack` positioned to match one of the
needles and also the 1-based index of the matching element in $(D
needles) (0 if none of `needles` matched, 1 if `needles[0]`
matched, 2 if `needles[1]` matched...). The first needle to be found
will be the one that matches. If multiple needles are found at the
same spot in the range, then the shortest one is the one which matches
(if multiple needles of the same length are found at the same spot (e.g
`"a"` and `'a'`), then the left-most of them in the argument list
matches).

The relationship between `haystack` and `needles` simply means
that one can e.g. search for individual `int`s or arrays of $(D
int)s in an array of `int`s. In addition, if elements are
individually comparable, searches of heterogeneous types are allowed
as well: a `double[]` can be searched for an `int` or a $(D
short[]), and conversely a `long` can be searched for a `float`
or a `double[]`. This makes for efficient searches without the need
to coerce one side of the comparison into the other's side type.

The complexity of the search is $(BIGOH haystack.length *
max(needles.length)). (For needles that are individual items, length
is considered to be 1.) The strategy used in searching several
subranges at once maximizes cache usage by moving in `haystack` as
few times as possible.
 */
Tuple!(Range, size_t) find(alias pred = "a == b", Range, Ranges...)
(Range haystack, Ranges needles)
if (Ranges.length > 1 && is(typeof(startsWith!pred(haystack, needles))))
{
    for (;; haystack.popFront())
    {
        size_t r = startsWith!pred(haystack, needles);
        if (r || haystack.empty)
        {
            return tuple(haystack, r);
        }
    }
}

///
@safe unittest
{
    import std.typecons : tuple;
    int[] a = [ 1, 4, 2, 3 ];
    assert(find(a, 4) == [ 4, 2, 3 ]);
    assert(find(a, [ 1, 4 ]) == [ 1, 4, 2, 3 ]);
    assert(find(a, [ 1, 3 ], 4) == tuple([ 4, 2, 3 ], 2));
    // Mixed types allowed if comparable
    assert(find(a, 5, [ 1.2, 3.5 ], 2.0) == tuple([ 2, 3 ], 3));
}

@safe unittest
{
    auto s1 = "Mary has a little lamb";
    assert(find(s1, "has a", "has an") == tuple("has a little lamb", 1));
    assert(find(s1, 't', "has a", "has an") == tuple("has a little lamb", 2));
    assert(find(s1, 't', "has a", 'y', "has an") == tuple("y has a little lamb", 3));
    assert(find("abc", "bc").length == 2);
}

@safe unittest
{
    import std.algorithm.internal : rndstuff;
    import std.meta : AliasSeq;
    import std.uni : toUpper;

    int[] a = [ 1, 2, 3 ];
    assert(find(a, 5).empty);
    assert(find(a, 2) == [2, 3]);

    foreach (T; AliasSeq!(int, double))
    {
        auto b = rndstuff!(T)();
        if (!b.length) continue;
        b[$ / 2] = 200;
        b[$ / 4] = 200;
        assert(find(b, 200).length == b.length - b.length / 4);
    }

    // Case-insensitive find of a string
    string[] s = [ "Hello", "world", "!" ];
    assert(find!("toUpper(a) == toUpper(b)")(s, "hello").length == 3);

    static bool f(string a, string b) { return toUpper(a) == toUpper(b); }
    assert(find!(f)(s, "hello").length == 3);
}

@safe unittest
{
    import std.algorithm.comparison : equal;
    import std.algorithm.internal : rndstuff;
    import std.meta : AliasSeq;
    import std.range : retro;

    int[] a = [ 1, 2, 3, 2, 6 ];
    assert(find(retro(a), 5).empty);
    assert(equal(find(retro(a), 2), [ 2, 3, 2, 1 ][]));

    foreach (T; AliasSeq!(int, double))
    {
        auto b = rndstuff!(T)();
        if (!b.length) continue;
        b[$ / 2] = 200;
        b[$ / 4] = 200;
        assert(find(retro(b), 200).length ==
                b.length - (b.length - 1) / 2);
    }
}

@safe unittest
{
    import std.algorithm.comparison : equal;
    import std.internal.test.dummyrange;

    int[] a = [ -1, 0, 1, 2, 3, 4, 5 ];
    int[] b = [ 1, 2, 3 ];
    assert(find(a, b) == [ 1, 2, 3, 4, 5 ]);
    assert(find(b, a).empty);

    foreach (DummyType; AllDummyRanges)
    {
        DummyType d;
        auto findRes = find(d, 5);
        assert(equal(findRes, [5,6,7,8,9,10]));
    }
}

/**
 * Finds `needle` in `haystack` efficiently using the
 * $(LINK2 https://en.wikipedia.org/wiki/Boyer%E2%80%93Moore_string_search_algorithm,
 * Boyer-Moore) method.
 *
 * Params:
 * haystack = A random-access range with length and slicing.
 * needle = A $(LREF BoyerMooreFinder).
 *
 * Returns:
 * `haystack` advanced such that `needle` is a prefix of it (if no
 * such position exists, returns `haystack` advanced to termination).
 */
RandomAccessRange find(RandomAccessRange, alias pred, InputRange)(
    RandomAccessRange haystack, scope BoyerMooreFinder!(pred, InputRange) needle)
{
    return needle.beFound(haystack);
}

@safe unittest
{
    string h = "/homes/aalexand/d/dmd/bin/../lib/libphobos.a(dmain2.o)"~
        "(.gnu.linkonce.tmain+0x74): In function `main' undefined reference"~
        " to `_Dmain':";
    string[] ns = ["libphobos", "function", " undefined", "`", ":"];
    foreach (n ; ns)
    {
        auto p = find(h, boyerMooreFinder(n));
        assert(!p.empty);
    }
}

///
@safe unittest
{
    import std.range.primitives : empty;
    int[] a = [ -1, 0, 1, 2, 3, 4, 5 ];
    int[] b = [ 1, 2, 3 ];

    assert(find(a, boyerMooreFinder(b)) == [ 1, 2, 3, 4, 5 ]);
    assert(find(b, boyerMooreFinder(a)).empty);
}

@safe unittest
{
    auto bm = boyerMooreFinder("for");
    auto match = find("Moor", bm);
    assert(match.empty);
}

// canFind
/++
Convenience function. Like find, but only returns whether or not the search
was successful.

See_Also:
$(REF among, std,algorithm,comparison) for checking a value against multiple possibilities.
 +/
template canFind(alias pred="a == b")
{
    import std.meta : allSatisfy;

    /++
    Returns `true` if and only if any value `v` found in the
    input range `range` satisfies the predicate `pred`.
    Performs (at most) $(BIGOH haystack.length) evaluations of `pred`.
     +/
    bool canFind(Range)(Range haystack)
    if (is(typeof(find!pred(haystack))))
    {
        return any!pred(haystack);
    }

    /++
    Returns `true` if and only if `needle` can be found in $(D
    range). Performs $(BIGOH haystack.length) evaluations of `pred`.
     +/
    bool canFind(Range, Element)(Range haystack, scope Element needle)
    if (is(typeof(find!pred(haystack, needle))))
    {
        return !find!pred(haystack, needle).empty;
    }

    /++
    Returns the 1-based index of the first needle found in `haystack`. If no
    needle is found, then `0` is returned.

    So, if used directly in the condition of an if statement or loop, the result
    will be `true` if one of the needles is found and `false` if none are
    found, whereas if the result is used elsewhere, it can either be cast to
    `bool` for the same effect or used to get which needle was found first
    without having to deal with the tuple that `LREF find` returns for the
    same operation.
     +/
    size_t canFind(Range, Ranges...)(Range haystack, scope Ranges needles)
    if (Ranges.length > 1 &&
        allSatisfy!(isForwardRange, Ranges) &&
        is(typeof(find!pred(haystack, needles))))
    {
        return find!pred(haystack, needles)[1];
    }
}

///
@safe unittest
{
    assert(canFind([0, 1, 2, 3], 2) == true);
    assert(canFind([0, 1, 2, 3], [1, 2], [2, 3]));
    assert(canFind([0, 1, 2, 3], [1, 2], [2, 3]) == 1);
    assert(canFind([0, 1, 2, 3], [1, 7], [2, 3]));
    assert(canFind([0, 1, 2, 3], [1, 7], [2, 3]) == 2);

    assert(canFind([0, 1, 2, 3], 4) == false);
    assert(!canFind([0, 1, 2, 3], [1, 3], [2, 4]));
    assert(canFind([0, 1, 2, 3], [1, 3], [2, 4]) == 0);
}

/**
 * Example using a custom predicate.
 * Note that the needle appears as the second argument of the predicate.
 */
@safe unittest
{
    auto words = [
        "apple",
        "beeswax",
        "cardboard"
    ];
    assert(!canFind(words, "bees"));
    assert( canFind!((string a, string b) => a.startsWith(b))(words, "bees"));
}

@safe unittest
{
    import std.algorithm.internal : rndstuff;

    auto a = rndstuff!(int)();
    if (a.length)
    {
        auto b = a[a.length / 2];
        assert(canFind(a, b));
    }
}

@safe unittest
{
    import std.algorithm.comparison : equal;
    assert(equal!(canFind!"a < b")([[1, 2, 3], [7, 8, 9]], [2, 8]));
}