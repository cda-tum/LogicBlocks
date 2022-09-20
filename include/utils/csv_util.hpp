#ifndef CSV_UTIL
#define CSV_UTIL
#include <iostream>
#include <set>
#include <vector>

namespace csv {
    inline std::vector<std::string>
    parseLine(const std::string& line, const std::set<char>& escapeChars,
              const std::set<char>& ignoredChars) {
        std::vector<std::string> result;
        std::string              word;
        bool                     inEscape = false;
        for (char c: line) {
            if (ignoredChars.find(c) != ignoredChars.end()) {
                continue;
            }
            if (inEscape) {
                if (escapeChars.find(c) != escapeChars.end()) {
                    word += c;
                    inEscape = false;
                } else {
                    word += c;
                }
            } else {
                if (escapeChars.find(c) != escapeChars.end()) {
                    inEscape = true;
                } else if (c == ',') {
                    result.push_back(word);
                    word = "";
                } else {
                    word += c;
                }
            }
        }
        result.push_back(word);
        return result;
    };

} // namespace csv

#endif // CSV_UTIL
