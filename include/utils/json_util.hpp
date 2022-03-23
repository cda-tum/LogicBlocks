#ifndef JSON_UTIL
#define JSON_UTIL
#include <functional>
#include <iostream>
#include <map>
#include <string>
#include <tuple>
#include <utility>

namespace JSON {

    template<typename T, T... S, typename F>
    constexpr void for_sequence(std::integer_sequence<T, S...>, F&& f) {
        using unpack_t = int[];
        (void)unpack_t{(static_cast<void>(f(std::integral_constant<T, S>{})), 0)...,
                       0};
    }

    struct Value;

    struct ValueData {
        std::map<std::string, Value> subObject;
        std::string                  string;
    };

    struct Value {
        ValueData data;

        Value() = default;
        Value& operator[](std::string name) {
            return data.subObject[std::move(name)];
        }

        const Value& operator[](const std::string& name) const {
            auto it = data.subObject.find(name);

            if (it != data.subObject.end()) {
                return it->second;
            }

            throw;
        }

        Value& operator=(std::string value) {
            data.string = std::move(value);
            return *this;
        }
    };

    template<typename T>
    inline T& asAny(Value&);
    template<typename T>
    inline const T& asAny(const Value&);

    template<>
    inline const std::string& asAny<std::string>(const Value& value) {
        return value.data.string;
    }

    template<>
    inline std::string& asAny<std::string>(Value& value) {
        return value.data.string;
    }

    template<typename T>
    inline std::string fromAny(T&);
    template<typename T>
    inline std::string fromAny(const T&);
    template<typename T>
    inline void toAny(T&, const std::string&);

#define JSON_STD_FROM(T)                            \
    template<>                                      \
    inline std::string fromAny<T>(T & value) {      \
        return std::to_string(value);               \
    }                                               \
    template<>                                      \
    inline std::string fromAny<T>(const T& value) { \
        return std::to_string(value);               \
    }

#define JSON_FROM(T, toString)                            \
    template<>                                            \
    inline std::string JSON::fromAny<T>(T & value) {      \
        return toString(value);                           \
    }                                                     \
    template<>                                            \
    inline std::string JSON::fromAny<T>(const T& value) { \
        return toString(value);                           \
    }

    JSON_STD_FROM(int)
    JSON_STD_FROM(unsigned int)
    JSON_STD_FROM(long)
    JSON_STD_FROM(unsigned long)
    JSON_STD_FROM(long long)
    JSON_STD_FROM(unsigned long long)
    JSON_STD_FROM(float)
    JSON_STD_FROM(double)
    JSON_STD_FROM(bool)
    JSON_STD_FROM(short)
    JSON_STD_FROM(unsigned short)
    JSON_STD_FROM(char)
    JSON_STD_FROM(unsigned char)

    template<>
    inline void toAny<int>(int& value, const std::string& str) {
        value = std::stoi(str);
    }

    template<typename Class, typename T>
    struct PropertyImpl {
        constexpr PropertyImpl(T Class::*aMember, const char* aName):
            member{aMember}, name{aName} {}

        using Type = T;

        T Class::*  member;
        const char* name;
    };

    template<typename Class, typename T>
    static constexpr auto property(T Class::*member, const char* name) {
        return PropertyImpl<Class, T>{member, name};
    };

    template<typename T>
    inline Value toJson(const T& object) {
        Value data;

        constexpr auto nbProperties = std::tuple_size<decltype(T::properties)>::value;

        for_sequence(std::make_index_sequence<nbProperties>{}, [&](auto i) {
            constexpr auto property         = std::get<i>(T::properties);
            data[property.name].data.string = fromAny(object.*(property.member));
        });

        return data;
    }

} // namespace JSON

#endif // JSON_UTIL
