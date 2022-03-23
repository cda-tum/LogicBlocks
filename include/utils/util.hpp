//
// Created by Sarah on 12.07.2021.
//

#ifndef CLIFFORDSATOPT_UTIL_H
#define CLIFFORDSATOPT_UTIL_H
#include <algorithm>
#include <boost/log/core.hpp>
#include <boost/log/exceptions.hpp>
#include <boost/log/expressions.hpp>
#include <boost/log/sinks/text_file_backend.hpp>
#include <boost/log/sources/record_ostream.hpp>
#include <boost/log/sources/severity_logger.hpp>
#include <boost/log/trivial.hpp>
#include <boost/log/utility/setup/common_attributes.hpp>
#include <boost/log/utility/setup/console.hpp>
#include <boost/log/utility/setup/file.hpp>

#include <cmath>
#include <iostream>
#include <iterator>
#include <map>
#include <memory>
#include <ostream>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace logging = boost::log;
namespace sinks = boost::log::sinks;
namespace keywords = boost::log::keywords;

namespace util {
#define ERROR() BOOST_LOG_TRIVIAL(error)
#define WARNING() BOOST_LOG_TRIVIAL(warning)
#define INFO() BOOST_LOG_TRIVIAL(info)
#define DEBUG() BOOST_LOG_TRIVIAL(debug)
#define TRACE() BOOST_LOG_TRIVIAL(trace)

inline void init(const std::string &logfile = "") {
  if (logfile != "" && logfile != "std") {
    logging::add_file_log(keywords::file_name = logfile,
                          keywords::rotation_size = 10 * 1024 * 1024,
                          keywords::time_based_rotation =
                              sinks::file::rotation_at_time_point(0, 0, 0),
                          keywords::format = "[%TimeStamp%]: %Message%",
                          keywords::auto_flush = true);
  } else if (logfile == "std")
    logging::add_console_log(std::cout,
                             keywords::format = "[%TimeStamp%]: %Message%");
}

inline void fatal(const std::string &msg) {
  BOOST_LOG_TRIVIAL(fatal) << msg;
  throw std::runtime_error(msg);
}
inline void error(const std::string &msg) { BOOST_LOG_TRIVIAL(error) << msg; }
inline void warning(const std::string &msg) {
  BOOST_LOG_TRIVIAL(warning) << msg;
}
inline void info(const std::string &msg) { BOOST_LOG_TRIVIAL(info) << msg; }
inline void debug(const std::string &msg) { BOOST_LOG_TRIVIAL(debug) << msg; }
inline void trace(const std::string &msg) { BOOST_LOG_TRIVIAL(trace) << msg; }

template <typename... Args>
inline std::string string_format(const std::string &format, Args... args) {
  int size_s = std::snprintf(nullptr, 0, format.c_str(), args...) +
               1; // Extra space for '\0'
  if (size_s <= 0) {
    error("Error during formatting.");
  }
  auto size = static_cast<size_t>(size_s);
  auto buf = std::make_unique<char[]>(size);
  std::snprintf(buf.get(), size, format.c_str(), args...);
  return std::string(buf.get(),
                     buf.get() + size - 1); // We don't want the '\0' inside
};

inline void pretty(const std::vector<std::vector<short>> &tableau,
                   std::ostream &os = std::cout) {
  if (tableau.empty()) {
    debug("Empty tableau");
    return;
  }
  for (size_t i = 0; i < tableau.back().size(); ++i) {
    os << i << "\t";
  }
  os << std::endl;
  auto i = 1;
  for (const auto &row : tableau) {
    if (row.size() != tableau.back().size()) {
      fatal("Tableau is not rectangular");
    }
    os << i++ << "\t";
    for (const auto &s : row)
      os << s << '\t';
    os << std::endl;
  }
};
inline std::string pretty_s(const std::vector<std::vector<short>> &tableau) {
  std::stringstream ss;
  pretty(tableau, ss);
  return ss.str();
};

inline std::vector<std::set<unsigned short>>
subsets(const std::set<unsigned short> &input, int k) {
  size_t n = input.size();

  std::vector<std::set<unsigned short>> result;

  size_t i = (1 << k) - 1;

  while (!(i >> n)) {
    std::set<unsigned short> v;
    std::set<unsigned short>::iterator it = input.begin();
    for (size_t j = 0; j < n; j++) {
      if (i & (1 << j)) {
        v.insert(*it);
      }
      std::advance(it, 1);
    }

    result.push_back(v);

    i = (i + (i & (-i))) | (((i ^ (i + (i & (-i)))) >> 2) / (i & (-i)));
  }

  return result;
};

inline void
isFullyConnected(unsigned short node,
                 const std::vector<std::set<unsigned short>> &connections,
                 std::vector<bool> &visited) {
  if (visited.at(node))
    return;
  visited[node] = true;

  if (connections.at(node).empty()) {
    return;
  }

  for (auto child : connections.at(node)) {
    isFullyConnected(child, connections, visited);
  }
};

inline std::set<std::pair<unsigned short, unsigned short>>
getFullyConnectedMap(unsigned short nQubits) {
  std::set<std::pair<unsigned short, unsigned short>> result{};
  for (int q = 0; q < nQubits; ++q) {
    for (int p = q + 1; p < nQubits; ++p) {
      result.emplace(q, p);
      result.emplace(p, q);
    }
  }
  return result;
};

inline bool
isFullyConnected(const std::set<std::pair<unsigned short, unsigned short>> &cm,
                 int nQubits, const std::set<unsigned short> &qubitChoice) {
  std::vector<std::set<unsigned short>> connections;
  std::vector<int> d;
  std::vector<bool> visited;
  connections.resize(nQubits);
  for (auto edge : cm) {
    if ((qubitChoice.count(edge.first) && qubitChoice.count(edge.second)) ||
        (qubitChoice.count(edge.second) && qubitChoice.count(edge.first))) {
      connections.at(edge.first).insert(edge.second);
      connections.at(edge.second).insert(edge.first);
    }
  }
  for (auto q : qubitChoice) {
    visited.clear();
    visited.resize(nQubits);
    std::fill(visited.begin(), visited.end(), false);
    isFullyConnected(q, connections, visited);
    for (auto p : qubitChoice) {
      if (!visited.at(p))
        return false;
    }
  }
  return true;
};
inline bool checkEquality(const std::vector<std::vector<short>> &tableau1,
                          const std::vector<std::vector<short>> &tableau2,
                          int nqubits) {
  if (tableau1.size() != tableau2.size())
    return false;
  for (int i = 0; i < nqubits; ++i) {
    if (tableau1.at(i).size() != tableau2.at(i).size())
      return false;
    for (int j = 0; j < 2 * nqubits + 1; ++j) {
      if (tableau1[i][j] != tableau2[i][j])
        return false;
    }
  }
  return true;
};

inline void
printCouplingMap(const std::set<std::pair<unsigned short, unsigned short>> &cm,
                 std::ostream &os) {
  os << "{";
  for (auto edge : cm) {
    os << "(" << edge.first << " " << edge.second << ") ";
  }
  os << "}" << std::endl;
};
inline std::string printCouplingMap(
    const std::set<std::pair<unsigned short, unsigned short>> &cm) {
  std::stringstream ss;
  printCouplingMap(cm, ss);
  return ss.str();
};
inline void
printFidelities(const std::vector<double> &singleFidelities,
                const std::vector<std::vector<double>> &doubleFidelities,
                std::ostream &os) {
  os << "Single fidelities: ";
  int i = 0;
  for (auto f : singleFidelities) {
    os << "Qubit " << i++ << " = " << f << " ";
  }
  os << std::endl;
  os << "Double fidelities: ";
  int j = 0;
  for (auto f : doubleFidelities) {
    i = 0;
    for (auto f2 : f) {
      os << "Edge "
         << "(" << i++ << "," << j << ") = " << f2 << " ";
    }
    os << std::endl;
    j++;
  }
}
inline std::string
printFidelities(const std::vector<double> &singleFidelities,
                const std::vector<std::vector<double>> &doubleFidelities) {
  std::stringstream ss;
  printFidelities(singleFidelities, doubleFidelities, ss);
  return ss.str();
}

}; // namespace util

#endif // CLIFFORDSATOPT_UTIL_H
