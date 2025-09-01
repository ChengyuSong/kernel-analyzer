#pragma once

// Macros for encoding/decoding keys
#define COMBINE(i, j) ((ull)i << 32 | j & 0xFFFFFFFFULL)
#define COMBINE_INT(i, j, k) ((int64_t)(((int64_t)i << 32) | ((int64_t)j << 8) | (int64_t)k))
#define CANTOR2(a, b) ((a + b + 1) * (a + b) / 2 + b)
#define CANTOR3(a, b, c) (CANTOR2(a, CANTOR2(b, c)))
#define LEFT(i) ((int)(i >> 32))
#define RIGHT(i) ((int)i)

namespace gracfl {
    using uint = unsigned int;
    using ull = unsigned long long;
}