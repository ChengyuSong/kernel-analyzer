#pragma once

#include <vector>

#include "Types.hpp"

#if defined(GRACFL_USE_STD_UNORDERED_SET)
#include <unordered_set>
#else
#include "boost/unordered/unordered_flat_set.hpp"
#endif

namespace gracfl {
    // Reachability set used by CFL solvers. Default is boost::unordered_flat_set
    // (lower overhead at very large edge counts). Define GRACFL_USE_STD_UNORDERED_SET
    // to compare against std::unordered_set.
#if defined(GRACFL_USE_STD_UNORDERED_SET)
    // Match the pre-refactor GraCFL storage as closely as possible.
    // (Original code used std::unordered_set<ull> for reachability.)
    using ReachabilitySet = std::unordered_set<ull>;
    inline constexpr const char* kReachabilitySetKind = "std::unordered_set<ull>";
#else
    using ReachabilitySet = boost::unordered_flat_set<uint>;
    inline constexpr const char* kReachabilitySetKind = "boost::unordered_flat_set<uint>";
#endif

    using ReachabilityMatrix = std::vector<std::vector<ReachabilitySet>>;
}
