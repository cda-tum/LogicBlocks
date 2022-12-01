#ifndef LOGGING_UTIL_H
#define LOGGING_UTIL_H

#include <exception>
#include <iostream>
#include <plog/Appenders/ColorConsoleAppender.h>
#include <plog/Appenders/RollingFileAppender.h>
#include <plog/Formatters/TxtFormatter.h>
#include <plog/Init.h>
#include <plog/Log.h>
#include <string>

namespace util {

#define TRACE() PLOG_VERBOSE
#define DEBUG() PLOG_DEBUG
#define INFO() PLOG_INFO
#define WARNING() PLOG_WARNING
#define ERROR() PLOG_ERROR
#define FATAL() PLOG_FATAL

    inline void init(const std::string& logfile = "", plog::Severity severity = plog::verbose) {
        if (!logfile.empty() && logfile != "std") {
            static plog::RollingFileAppender<plog::TxtFormatter> fileAppender(logfile.c_str());
            plog::init(severity, &fileAppender);
        } else if (logfile == "std" || logfile.empty()) {
            static plog::ColorConsoleAppender<plog::TxtFormatter> consoleAppender;
            plog::init(severity, &consoleAppender);
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
