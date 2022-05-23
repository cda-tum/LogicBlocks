//
// Created by Sarah on 12.07.2021.
//

#ifndef LOGGING_UTIL_H
#define LOGGING_UTIL_H

#include <exception>
#include <iostream>
#include <string>


namespace util {
//#define ERROR() BOOST_LOG_TRIVIAL(error)
//#define WARNING() BOOST_LOG_TRIVIAL(warning)
//#define INFO() BOOST_LOG_TRIVIAL(info)
//#define DEBUG() BOOST_LOG_TRIVIAL(debug)
//#define TRACE() BOOST_LOG_TRIVIAL(trace)

    inline void init(const std::string& logfile = "") {
//        if (!logfile.empty() && logfile != "std") {
//            logging::add_file_log(keywords::file_name           = logfile,
//                                  keywords::rotation_size       = 10 * 1024 * 1024,
//                                  keywords::time_based_rotation = sinks::file::rotation_at_time_point(0, 0, 0),
//                                  keywords::format              = "[%TimeStamp%]: %Message%",
//                                  keywords::auto_flush          = true);
//        } else if (logfile == "std") {
//            logging::add_console_log(std::cout, keywords::format = "[%TimeStamp%]: %Message%");
//        }
    }

    inline void fatal(const std::string& msg) {
//        BOOST_LOG_TRIVIAL(fatal) << msg;
        throw std::runtime_error(msg);
    }
    inline void error(const std::string& msg) {
//        BOOST_LOG_TRIVIAL(error) << msg;
    }
    inline void warning(const std::string& msg) {
//        BOOST_LOG_TRIVIAL(warning) << msg;
    }
    inline void info(const std::string& msg) {
//        BOOST_LOG_TRIVIAL(info) << msg;
    }
    inline void debug(const std::string& msg) {
//        BOOST_LOG_TRIVIAL(debug) << msg;
    }
    inline void trace(const std::string& msg) {
//        BOOST_LOG_TRIVIAL(trace) << msg;
    }
} // namespace util

#endif // LOGGING_UTIL_H
