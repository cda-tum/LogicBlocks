//
// Created by Sarah on 12.07.2021.
//

#ifndef LOGGING_UTIL_H
#define LOGGING_UTIL_H

#include <plog/Log.h>
#include <plog/Init.h>
#include <plog/Appenders/RollingFileAppender.h>
#include <plog/Appenders/ConsoleAppender.h>
#include <plog/Formatters/TxtFormatter.h>
#include <exception>
#include <iostream>
#include <string>


namespace util {

    inline void init(const std::string& logfile = "") {
        if (!logfile.empty() && logfile != "std") {
            static plog::RollingFileAppender<plog::TxtFormatter> fileAppender(logfile.c_str());
            plog::init(plog::verbose,&fileAppender);
        } else if (logfile == "std") {
            static plog::ConsoleAppender<plog::TxtFormatter> consoleAppender;
            plog::init(plog::verbose, &consoleAppender);
        }
    }

    inline void fatal(const std::string& msg) {
        PLOG_FATAL << msg;
        throw std::runtime_error(msg);
    }
    inline void error(const std::string& msg) {
        PLOG_ERROR << msg;
    }
    inline void warning(const std::string& msg) {
        PLOG_WARNING << msg;
    }
    inline void info(const std::string& msg) {
        PLOG_INFO << msg;
    }
    inline void debug(const std::string& msg) {
        PLOG_DEBUG << msg;
    }
    inline void trace(const std::string& msg) {
        PLOG_VERBOSE << msg;
    }
} // namespace util

#endif // LOGGING_UTIL_H
