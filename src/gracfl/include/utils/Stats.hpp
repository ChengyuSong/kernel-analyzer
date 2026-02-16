#pragma once

#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <limits>
#include <string>

namespace gracfl::stats {
    inline bool getenv_bool(const char* name, bool defaultValue = false)
    {
        const char* v = std::getenv(name);
        if (!v) return defaultValue;
        if (*v == '\0') return true;
        return std::atoi(v) != 0;
    }

    inline int getenv_int(const char* name, int defaultValue)
    {
        const char* v = std::getenv(name);
        if (!v || *v == '\0') return defaultValue;
        return std::atoi(v);
    }

    // Current resident set size in kB (Linux /proc).
    inline std::uint64_t rss_kb()
    {
        std::ifstream f("/proc/self/status");
        if (!f.is_open())
            return 0;

        std::string key;
        while (f >> key) {
            if (key == "VmRSS:") {
                std::uint64_t value = 0;
                std::string unit;
                f >> value >> unit;
                return value; // already in kB
            }
            f.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
        }
        return 0;
    }
}

