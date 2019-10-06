#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <vector>
#include <iomanip>
#include <chrono>
#if defined(WIN32) || defined(_WIN32) || defined(__WIN32) && !defined(__CYGWIN__)
#define WINDOWS
#include "windows.h"
#else
#define LINUX
#include <dlfcn.h>
#endif

namespace libs {

    const int bigint_base = 1000000000;
    const int bigint_base_digits = 9;


    typedef   signed char        int8;
    typedef unsigned char       uint8;
    typedef   signed short      int16;
    typedef unsigned short     uint16;
    typedef   signed int        int32;
    typedef unsigned int       uint32;
    typedef   signed long long  int64;
    typedef unsigned long long uint64;
    typedef float             float32;
    typedef double            float64;

    namespace math {
        int64 pow(int64 num, int64 exp) {
            if (exp < 0)
                return 0;
            int64 result(1);
            while (exp > 0) {
                if (exp % 2 == 1) {
                    result *= num;
                }
                exp /= 2;
                num *= num;
            }
            return result;
        }
        int32 pow(int32 num, int32 exp) {
            if (exp < 0)
                return 0;
            int64 result(1);
            while (exp > 0) {
                if (exp % 2 == 1) {
                    result *= num;
                }
                exp /= 2;
                num *= num;
            }
            return result;
        }
        int64 int_from_string(char* str) {
            uint64 result = 0;
            bool negative = false;
            char c = *(str++);
            if (c == '-') {
                negative = true;
            }

            if (c == '-' || c == '+')
                c = *(str++);

            for (; c > 47 && c < 58; c = *(str++))
                result = (result << 1) * 5 + c - 48;

            return (negative ? -int64(result) : result);
        }
        float64 double_from_string(char* str) {
            bool negative = false;
            int c;

            float64 number = 0;

            c = *(str++);
            if (c == '-') {
                negative = true;
            }

            if (c == '-' || c == '+')
                c = *(str++);

            for (; (c > 47 && c < 58); c = *(str++))
                number = number * 10 + c - 48;

            if (c == '.') {
                c = *(str++);
                for (double i = 1; c > 47 && c < 58; c = *(str++))
                    number += (i /= 10) * (c - 48);
            }

            if (c == 'e' || c == 'E') {
                long pow = int_from_string(str);
                if (pow > 0) {
                    while (pow-- > 0)
                        number *= 10;
                } else if (pow < 0) {
                    while (pow++ < 0)
                        number /= 10;
                }
            }

            if (negative)
                number *= -1;
            return number;
        }
    }

    struct bigint {
        std::vector<int> a;
        int sign;

        bigint() :
                sign(1) {
        }

        bigint(long long v) {
            *this = v;
        }

        bigint(const std::string &s) {
            read(s);
        }

        bigint& operator=(const bigint &v) = default;

        bigint& operator=(long long v) {
            sign = 1;
            if (v < 0)
                sign = -1, v = -v;
            for (; v > 0; v = v / bigint_base)
                a.push_back(v % bigint_base);
            return *this;
        }

        bigint operator+(const bigint &v) const {
            if (sign == v.sign) {
                bigint res = v;

                for (int i = 0, carry = 0; i < (int) std::max(a.size(), v.a.size()) || carry; ++i) {
                    if (i == (int) res.a.size())
                        res.a.push_back(0);
                    res.a[i] += carry + (i < (int) a.size() ? a[i] : 0);
                    carry = res.a[i] >= bigint_base;
                    if (carry)
                        res.a[i] -= bigint_base;
                }
                return res;
            }
            return *this - (-v);
        }

        bigint operator-(const bigint &v) const {
            if (sign == v.sign) {
                if (abs() >= v.abs()) {
                    bigint res = *this;
                    for (int i = 0, carry = 0; i < (int) v.a.size() || carry; ++i) {
                        res.a[i] -= carry + (i < (int) v.a.size() ? v.a[i] : 0);
                        carry = res.a[i] < 0;
                        if (carry)
                            res.a[i] += bigint_base;
                    }
                    res.trim();
                    return res;
                }
                return -(v - *this);
            }
            return *this + (-v);
        }

        void operator*=(int v) {
            if (v < 0)
                sign = -sign, v = -v;
            for (int i = 0, carry = 0; i < (int) a.size() || carry; ++i) {
                if (i == (int) a.size())
                    a.push_back(0);
                long long cur = a[i] * (long long) v + carry;
                carry = (int) (cur / bigint_base);
                a[i] = (int) (cur % bigint_base);
                //asm("divl %%ecx" : "=a"(carry), "=d"(a[i]) : "A"(cur), "c"(bigint_base));
            }
            trim();
        }

        bigint operator*(int v) const {
            bigint res = *this;
            res *= v;
            return res;
        }

        friend std::pair<bigint, bigint> divmod(const bigint &a1, const bigint &b1) {
            int norm = bigint_base / (b1.a.back() + 1);
            bigint a = a1.abs() * norm;
            bigint b = b1.abs() * norm;
            bigint q, r;
            q.a.resize(a.a.size());

            for (int i = a.a.size() - 1; i >= 0; i--) {
                r *= bigint_base;
                r += a.a[i];
                int s1 = r.a.size() <= b.a.size() ? 0 : r.a[b.a.size()];
                int s2 = r.a.size() <= b.a.size() - 1 ? 0 : r.a[b.a.size() - 1];
                int d = ((long long) bigint_base * s1 + s2) / b.a.back();
                r -= b * d;
                while (r < 0)
                    r += b, --d;
                q.a[i] = d;
            }

            q.sign = a1.sign * b1.sign;
            r.sign = a1.sign;
            q.trim();
            r.trim();
            return std::make_pair(q, r / norm);
        }

        bigint operator/(const bigint &v) const {
            return divmod(*this, v).first;
        }

        bigint operator%(const bigint &v) const {
            return divmod(*this, v).second;
        }

        void operator/=(int v) {
            if (v < 0)
                sign = -sign, v = -v;
            for (int i = (int) a.size() - 1, rem = 0; i >= 0; --i) {
                long long cur = a[i] + rem * (long long) bigint_base;
                a[i] = (int) (cur / v);
                rem = (int) (cur % v);
            }
            trim();
        }

        bigint operator/(int v) const {
            bigint res = *this;
            res /= v;
            return res;
        }

        int operator%(int v) const {
            if (v < 0)
                v = -v;
            int m = 0;
            for (int i = a.size() - 1; i >= 0; --i)
                m = (a[i] + m * (long long) bigint_base) % v;
            return m * sign;
        }

        void operator+=(const bigint &v) {
            *this = *this + v;
        }

        void operator-=(const bigint &v) {
            *this = *this - v;
        }

        void operator*=(const bigint &v) {
            *this = *this * v;
        }

        void operator/=(const bigint &v) {
            *this = *this / v;
        }

        bool operator<(const bigint &v) const {
            if (sign != v.sign)
                return sign < v.sign;
            if (a.size() != v.a.size())
                return a.size() * sign < v.a.size() * v.sign;
            for (int i = a.size() - 1; i >= 0; i--)
                if (a[i] != v.a[i])
                    return a[i] * sign < v.a[i] * sign;
            return false;
        }

        bool operator>(const bigint &v) const {
            return v < *this;
        }

        bool operator<=(const bigint &v) const {
            return !(v < *this);
        }

        bool operator>=(const bigint &v) const {
            return !(*this < v);
        }

        bool operator==(const bigint &v) const {
            return !(*this < v) && !(v < *this);
        }

        bool operator!=(const bigint &v) const {
            return *this < v || v < *this;
        }

        void trim() {
            while (!a.empty() && !a.back())
                a.pop_back();
            if (a.empty())
                sign = 1;
        }

        bool is_zero() const {
            return a.empty() || (a.size() == 1 && !a[0]);
        }

        bigint operator-() const {
            bigint res = *this;
            res.sign = -sign;
            return res;
        }

        bigint abs() const {
            bigint res = *this;
            res.sign *= res.sign;
            return res;
        }

        long long long_value() const {
            long long res = 0;
            for (int i = a.size() - 1; i >= 0; i--)
                res = res * bigint_base + a[i];
            return res * sign;
        }

        friend bigint gcd(const bigint &a, const bigint &b) {
            return b.is_zero() ? a : gcd(b, a % b);
        }

        friend bigint lcm(const bigint &a, const bigint &b) {
            return a / gcd(a, b) * b;
        }

        bigint pow(bigint b) const {
            bigint result(1);
            bigint a = *this;
            while (b > 0) {
                if (b % 2 == 1) {
                    result *= a;
                }
                b /= 2;
                a *= a;
            }
            return result;
        }

        bigint pow(long long b) const {
            bigint result(1);
            bigint a = *this;
            while (b > 0) {
                if (b % 2 == 1) {
                    result *= a;
                }
                b /= 2;
                a *= a;
            }
            return result;
        }

        bigint pow(long b) const {
            bigint result(1);
            bigint a = *this;
            while (b > 0) {
                if (b % 2 == 1) {
                    result *= a;
                }
                b /= 2;
                a *= a;
            }
            return result;
        }

        bigint pow(int b) const {
            bigint result(1);
            bigint a = *this;
            while (b > 0) {
                if (b % 2 == 1) {
                    result *= a;
                }
                b /= 2;
                a *= a;
            }
            return result;
        }

        bigint operator^(bigint other) {
            return pow(other);
        }

        bigint operator^(long other) {
            return pow(other);
        }

        bigint operator^(long long other) {
            return pow(other);
        }

        bigint operator^(int other) {
            return pow(other);
        }

        void read(const std::string &s) {
            sign = 1;
            a.clear();
            int pos = 0;
            while (pos < (int) s.size() && (s[pos] == '-' || s[pos] == '+')) {
                if (s[pos] == '-')
                    sign = -sign;
                ++pos;
            }
            for (int i = s.size() - 1; i >= pos; i -= bigint_base_digits) {
                int x = 0;
                for (int j = std::max(pos, i - bigint_base_digits + 1); j <= i; j++)
                    x = x * 10 + s[j] - '0';
                a.push_back(x);
            }
            trim();
        }

        friend std::istream &operator>>(std::istream &stream, bigint &v) {
            std::string s;
            stream >> s;
            v.read(s);
            return stream;
        }

        friend std::ostream &operator<<(std::ostream &stream, const bigint &v) {
            if (v.sign == -1)
                stream << '-';
            stream << (v.a.empty() ? 0 : v.a.back());
            for (int i = (int) v.a.size() - 2; i >= 0; --i)
                stream << std::setw(bigint_base_digits) << std::setfill('0') << v.a[i];
            return stream;
        }

        static std::vector<int> convert_base(const std::vector<int> &a, int old_digits, int new_digits) {
            std::vector<long long> p(std::max(old_digits, new_digits) + 1);
            p[0] = 1;
            for (int i = 1; i < (int) p.size(); i++)
                p[i] = p[i - 1] * 10;
            std::vector<int> res;
            long long cur = 0;
            int cur_digits = 0;
            for (int i = 0; i < (int) a.size(); i++) {
                cur += a[i] * p[cur_digits];
                cur_digits += old_digits;
                while (cur_digits >= new_digits) {
                    res.push_back(int(cur % p[new_digits]));
                    cur /= p[new_digits];
                    cur_digits -= new_digits;
                }
            }
            res.push_back((int) cur);
            while (!res.empty() && !res.back())
                res.pop_back();
            return res;
        }

        typedef std::vector<long long> vll;

        static vll karatsubaMultiply(const vll &a, const vll &b) {
            int n = a.size();
            vll res(n + n);
            if (n <= 32) {
                for (int i = 0; i < n; i++)
                    for (int j = 0; j < n; j++)
                        res[i + j] += a[i] * b[j];
                return res;
            }

            int k = n >> 1;
            vll a1(a.begin(), a.begin() + k);
            vll a2(a.begin() + k, a.end());
            vll b1(b.begin(), b.begin() + k);
            vll b2(b.begin() + k, b.end());

            vll a1b1 = karatsubaMultiply(a1, b1);
            vll a2b2 = karatsubaMultiply(a2, b2);

            for (int i = 0; i < k; i++)
                a2[i] += a1[i];
            for (int i = 0; i < k; i++)
                b2[i] += b1[i];

            vll r = karatsubaMultiply(a2, b2);
            for (int i = 0; i < (int) a1b1.size(); i++)
                r[i] -= a1b1[i];
            for (int i = 0; i < (int) a2b2.size(); i++)
                r[i] -= a2b2[i];

            for (int i = 0; i < (int) r.size(); i++)
                res[i + k] += r[i];
            for (int i = 0; i < (int) a1b1.size(); i++)
                res[i] += a1b1[i];
            for (int i = 0; i < (int) a2b2.size(); i++)
                res[i + n] += a2b2[i];
            return res;
        }

        bigint operator*(const bigint &v) const {
            std::vector<int> a6 = convert_base(this->a, bigint_base_digits, 6);
            std::vector<int> b6 = convert_base(v.a, bigint_base_digits, 6);
            vll a(a6.begin(), a6.end());
            vll b(b6.begin(), b6.end());
            while (a.size() < b.size())
                a.push_back(0);
            while (b.size() < a.size())
                b.push_back(0);
            while (a.size() & (a.size() - 1))
                a.push_back(0), b.push_back(0);
            vll c = karatsubaMultiply(a, b);
            bigint res;
            res.sign = sign * v.sign;
            for (int i = 0, carry = 0; i < (int) c.size(); i++) {
                long long cur = c[i] + carry;
                res.a.push_back((int) (cur % 1000000));
                carry = (int) (cur / 1000000);
            }
            res.a = convert_base(res.a, 6, bigint_base_digits);
            res.trim();
            return res;
        }
    };

    template<typename T>
    struct __fast_stdin_helper {
        void read(T &var) {
            std::cin >> var;
        }
    };

    template<>
    struct __fast_stdin_helper<int> {
        void read(int& number) {
            bool negative = false;
            int c;

            number = 0;

            while (std::isspace((unsigned char) (c = getchar()))) {}

            //c = getchar();
            if (c == '-') {
                negative = true;
                c = getchar();
            }

            for (; (c > 47 && c < 58); c = getchar())
                number = number * 10 + c - 48;

            if (negative)
                number *= -1;
        }
    };

    template<>
    struct __fast_stdin_helper<long> {
        void read(long& number) {
            bool negative = false;
            int c;

            number = 0;

            while (std::isspace((unsigned char) (c = getchar()))) {}

            //c = getchar();
            if (c == '-') {
                negative = true;
                c = getchar();
            }

            for (; (c > 47 && c < 58); c = getchar())
                number = number * 10 + c - 48;

            if (negative)
                number *= -1;
        }
    };

    template<>
    struct __fast_stdin_helper<long long> {
        void read(long long& number) {
            bool negative = false;
            int c;

            number = 0;

            while (std::isspace((unsigned char) (c = getchar()))) {}

            //c = getchar();
            if (c == '-') {
                negative = true;
                c = getchar();
            }

            for (; (c > 47 && c < 58); c = getchar())
                number = number * 10 + c - 48;

            if (negative)
                number *= -1;
        }
    };

    template<>
    struct __fast_stdin_helper<double> {
        void read(double& number) {
            bool negative = false;
            int c;

            number = 0;

            while (std::isspace((unsigned char) (c = getchar()))) {}

            //c = getchar();
            if (c == '-') {
                negative = true;
                c = getchar();
            }

            for (; (c > 47 && c < 58); c = getchar())
                number = number * 10 + c - 48;

            if (c == '.') {
                c = getchar();
                for (double i = 1; c > 47 && c < 58; c = getchar())
                    number += (i /= 10) * (c - 48);
            }

            if (c == 'e' || c == 'E') {
                long pow; __fast_stdin_helper<long>().read(pow);
                if (pow > 0) {
                    while (pow-- > 0)
                        number *= 10;
                } else if (pow < 0) {
                    while (pow++ < 0)
                        number /= 10;
                }
            }

            if (negative)
                number *= -1;
        }
    };

    class fast_stdin {
    public:
        fast_stdin() {
            std::ios_base::sync_with_stdio(false);
            std::ios::sync_with_stdio(false);
            std::cin.tie(0);
        }

        template<typename T>
        T read() {
            T result;
            read(result);
            return result;
        }

        template<typename T>
        fast_stdin &read(T &var) {
            __fast_stdin_helper<T>().read(var);
            return *this;
        }

        template<typename T>
        fast_stdin &operator>>(T &var) {
            return read(var);
        }
    };

    class fast_stdout {
    public:
        fast_stdout() {
            std::ios_base::sync_with_stdio(false);
            std::ios::sync_with_stdio(false);
        }

        template<typename T>
        fast_stdout &print(T var) {
            std::cout << var;
            return *this;
        }

        template<typename T>
        fast_stdout &println(T var) {
            print(var);
            println();
            return *this;
        }

        fast_stdout &println() {
            std::cout << '\n';
            return *this;
        }

        fast_stdout &flush() {
            std::cout << std::flush;
            return *this;
        }

        fast_stdout &set_precision(int precision) {
            std::cout << std::setprecision(precision);
            return *this;
        }

        fast_stdout &fixed() {
            std::cout << std::fixed;
            return *this;
        }
    };

    fast_stdin in;
    fast_stdout out;

#define DEBUG(x) libs::out.print(#x).print(" is ").println(x).flush()

    class __varargs_list {
    private:
        void *currentPtr;
    public:
        __varargs_list(void *currentPtr) : currentPtr(currentPtr) {}

        template<typename T>
        T &get() {
            return *(((T*&) currentPtr)++);
        }
    };

#define _INIT_VARARGS_1_ARG(last_arg) _INIT_VARARGS_2_ARG(last_arg, arguments)
#define _INIT_VARARGS_2_ARG(last_arg, name) libs::varargs_list name(&(last_arg) + 1)
#define _GET_ARG_3(arg1, arg2, arg3, ...) arg3
#define _INIT_VARARGS_CHOOSER(...) _GET_ARG_3(__VA_ARGS__, _INIT_VARARGS_2_ARG, _INIT_VARARGS_1_ARG)
#define INIT_VARARGS(...) _INIT_VARARGS_CHOOSER(__VA_ARGS__)(__VA_ARGS__)

    template<typename Return, typename ...Args>
    class function {
    public:
        typedef Return (*ptr)(Args...);
        typedef Return (__stdcall *ptr_stdcall)(Args...);
        typedef Return (&ref)(Args...);
        typedef Return (__stdcall &ref_stdcall)(Args...);

    private:
        ptr pointer;
    public:
        explicit function(ptr pointer) : pointer(pointer) {}

        Return operator()(Args... args) {
            return (*pointer)(args...);
        };
    };


    template<typename Return, typename ...Args>
    class function_test {
    public:
        typedef Return(*function_ptr)(Args...);

    private:
        std::streambuf *cin_buf;
        bool cin_buf_inited;
        signed long long int time_limit;
        bool time_limit_inited;
        const Return *expected_return;
        bool expected_return_inited;
        function_ptr func;

        void warn_if_cin_inited() {
            if (cin_buf_inited) std::cout << "WARNING: cin already inited, overriding" << std::endl;
        }

        void warn_if_time_limit_inited() {
            if (time_limit_inited) std::cout << "WARNING: time limit already inited, overriding" << std::endl;
        }

        void warn_if_expected_return_inited() {
            if (expected_return_inited) std::cout << "WARNING: expected return already inited, overriding" << std::endl;
        }

    public:
        function_test(function_ptr func) : func(func),
                                           cin_buf(0), cin_buf_inited(false),
                                           time_limit(-1), time_limit_inited(false),
                                           expected_return(0), expected_return_inited(false) {}

        function_test &with_standard_input() {
            warn_if_cin_inited();
            cin_buf = NULL;
            cin_buf_inited = true;
            return *this;
        }

        function_test &with_string_input(const std::string &input) {
            warn_if_cin_inited();
            static std::stringstream ss;
            ss << input;
            cin_buf = ss.rdbuf();
            cin_buf_inited = true;
            return *this;
        }

        function_test &with_file_input(const std::string &filename) {
            warn_if_cin_inited();
            cin_buf = new std::filebuf();
            ((std::filebuf *) cin_buf)->open(filename.c_str(), std::ios::in);
            cin_buf_inited = true;
            return *this;
        }

        function_test &with_time_limit(unsigned long int milliseconds) {
            warn_if_time_limit_inited();
            time_limit = milliseconds;
            time_limit_inited = true;
            return *this;
        }

        function_test &without_time_limit() {
            warn_if_time_limit_inited();
            time_limit = -1;
            time_limit_inited = true;
            return *this;
        }

        function_test &with_expected_return(const Return &_return) {
            warn_if_expected_return_inited();
            expected_return = &_return;
            expected_return_inited = true;
            return *this;
        };

        function_test &with_any_return() {
            warn_if_expected_return_inited();
            expected_return = NULL;
            expected_return_inited = true;
            return *this;
        }

        void run(Args... args) {
            std::streambuf *cin_backup = std::cin.rdbuf();
            if (cin_buf) {
                std::cin.rdbuf(cin_buf);
            }
            if (!cin_buf_inited) {
                std::cout << "WARNING: cin not inited, using standard input" << std::endl;
            }
            if (!expected_return_inited) {
                std::cout << "WARNING: expected return not inited, not checking return" << std::endl;
            }
            if (!time_limit_inited) {
                std::cout << "WARNING: time limit not inited, not limiting time" << std::endl;
            }
            std::cout << "Running function, output:" << std::endl;
            auto start = std::chrono::high_resolution_clock::now();
            Return value = (*func)(args...);
            auto end = std::chrono::high_resolution_clock::now();
            std::cout << std::endl;
            int errors = 0;
            int tests = 0;
            std::chrono::duration<double> elapsed = end - start;
            std::cout << "Function completed in " << (elapsed * 1000).count() << "ms";
            std::cout << std::endl;
            if (expected_return != NULL) {
                std::cout << "Test " << ++tests << ":" << std::endl;
                std::cout << "Checking return value..." << std::endl;
                if (value == *expected_return) {
                    std::cout << "Test completed, results are equal" << std::endl;
                } else {
                    std::cout << "Test failed, results are not equal" << std::endl;
                    errors++;
                }
            }
            if (time_limit >= 0) {
                std::cout << "Test " << ++tests << ":" << std::endl;
                std::cout << "Checking execution time, " << time_limit << "ms expected" << std::endl;
                if ((elapsed * 1000).count() < time_limit) {
                    std::cout << "Test completed, time limit not exceeded" << std::endl;
                } else {
                    std::cout << "Test failed, time limit exceeded" << std::endl;
                    errors++;
                }
            }
            std::cout << tests << " tests completed with " << errors << " errors" << std::endl;
        }
    };
    template <typename ...Args> class function_test<void, Args...> {
    public:
        typedef void(*function_ptr)(Args...);

    private:
        std::streambuf *cin_buf;
        bool cin_buf_inited;
        signed long long int time_limit;
        bool time_limit_inited;
        function_ptr func;

        void warn_if_cin_inited() {
            if (cin_buf_inited) std::cout << "WARNING: cin already inited, overriding" << std::endl;
        }

        void warn_if_time_limit_inited() {
            if (time_limit_inited) std::cout << "WARNING: time limit already inited, overriding" << std::endl;
        }

    public:
        function_test(function_ptr func) : func(func),
                                           cin_buf(0), cin_buf_inited(false),
                                           time_limit(-1), time_limit_inited(false) {}

        function_test &with_standard_input() {
            warn_if_cin_inited();
            cin_buf = NULL;
            cin_buf_inited = true;
            return *this;
        }

        function_test &with_string_input(const std::string &input) {
            warn_if_cin_inited();
            static std::stringstream ss;
            ss << input;
            cin_buf = ss.rdbuf();
            cin_buf_inited = true;
            return *this;
        }

        function_test &with_file_input(const std::string &filename) {
            warn_if_cin_inited();
            cin_buf = new std::filebuf();
            ((std::filebuf *) cin_buf)->open(filename.c_str(), std::ios::in);
            cin_buf_inited = true;
            return *this;
        }

        function_test &with_time_limit(unsigned long int milliseconds) {
            warn_if_time_limit_inited();
            time_limit = milliseconds;
            time_limit_inited = true;
            return *this;
        }

        function_test &without_time_limit() {
            warn_if_time_limit_inited();
            time_limit = -1;
            time_limit_inited = true;
            return *this;
        }

        void run(Args... args) {
            std::streambuf *cin_backup = std::cin.rdbuf();
            if (cin_buf) {
                std::cin.rdbuf(cin_buf);
            }
            if (!cin_buf_inited) {
                std::cout << "WARNING: cin not inited, using standard input" << std::endl;
            }
            if (!time_limit_inited) {
                std::cout << "WARNING: time limit not inited, not limiting time" << std::endl;
            }
            std::cout << "Running function, output:" << std::endl;
            auto start = std::chrono::high_resolution_clock::now();
            (*func)(args...);
            auto end = std::chrono::high_resolution_clock::now();
            std::cout << std::endl;
            int errors = 0;
            int tests = 0;
            std::chrono::duration<double> elapsed = end - start;
            std::cout << "Function completed in " << (elapsed * 1000).count() << "ms";
            std::cout << std::endl;
            if (time_limit >= 0) {
                std::cout << "Test " << ++tests << ":" << std::endl;
                std::cout << "Checking execution time, " << time_limit << "ms expected" << std::endl;
                if ((elapsed * 1000).count() < time_limit) {
                    std::cout << "Test completed, time limit not exceeded" << std::endl;
                } else {
                    std::cout << "Test failed, time limit exceeded" << std::endl;
                    errors++;
                }
            }
            std::cout << tests << " tests completed with " << errors << " errors" << std::endl;
        }
    };

    template<typename Return, typename ...Args>
    function_test<Return, Args...> test(Return (*func)(Args...)) {
        return function_test<Return, Args...>(func);
    }

    void sleep(int milliseconds) {
        clock_t time_end = clock() + milliseconds * CLOCKS_PER_SEC / 1000;
        while (clock() < time_end) {}
    }

    template<typename T, class alloc = std::allocator<T> >
    class collection {
    public:
        typedef T *pointer;
        typedef T &reference;
        typedef unsigned long long int size_type;

        class index_out_of_bounds : public std::exception {
        private:
            size_type i, length;
        public:
            const char *what() const throw();

            index_out_of_bounds(size_type i, size_type length);
        };

        class iterator {
        private:
            size_type i;
            collection *outer;
        public:
            iterator(size_type i, collection *outer);

            bool operator<(const iterator &rhs) const;

            bool operator>(const iterator &rhs) const;

            bool operator<=(const iterator &rhs) const;

            bool operator>=(const iterator &rhs) const;

            bool operator==(const iterator &rhs) const;

            bool operator!=(const iterator &rhs) const;

            iterator operator+(int i);

            iterator operator-(int i);

            iterator operator++();

            iterator operator++(int);

            iterator operator--();

            iterator operator--(int);

            T &operator*();
        };

    private:
        alloc allocator;
        T **element_storage;
        size_type length;
        size_type allocated_length;
        size_type buffer_size;

        void init() {
            length = 0;
            allocated_length = 0;
            buffer_size = 10;
            allocator = alloc();
            //preallocate(buffer_size);
        };
    public:
        collection();

        collection(size_type length, T (*func)(int));

        collection(size_type length, T);

        size_type size() const;

        collection& add(T value);

        collection& preallocate(size_type count);

        collection& add_all(collection another);

        reference get(size_type i) const;

        collection& set(size_type i, T value);

        collection& remove(size_type i);

        reference operator[](size_type i) const;

        collection operator+(T element);

        collection& set_buffer_size(const size_type& buffer_size);

        size_type get_buffer_size();

        iterator begin();

        iterator end();
    };

    template<typename T, class alloc>
    collection<T, alloc>& collection<T, alloc>::add(T value) {
        T *value_ptr = allocator.allocate(1);
        *value_ptr = value;

        /*T **new_storage = new pointer[length + 1];
        for (size_type i = 0; i < length; i++) {
            new_storage[i] = element_storage[i];
            //delete (element_storage + i);
        }

        new_storage[length] = value_ptr;
        element_storage = new_storage;*/

        if (length >= allocated_length)
            preallocate(buffer_size);

        element_storage[length] = value_ptr;

        length++;
        return *this;
    }

    template<typename T, class alloc>
    typename collection<T, alloc>::reference
    collection<T, alloc>::get(collection<T, alloc>::size_type i) const {
        if (i >= 0 && i < length) {
            return *(element_storage[i]);
        } else throw collection<T, alloc>::index_out_of_bounds(i, length);
    }

    template<typename T, class alloc>
    collection<T, alloc>::collection() {
        init();
    }

    template<typename T, class alloc>
    typename collection<T, alloc>::reference
    collection<T, alloc>::operator[](collection<T, alloc>::size_type i) const {
        return get(i);
    }

    template<typename T, class alloc>
    collection<T, alloc>&
    collection<T, alloc>::set(collection::size_type i, T value) {
        get(i) = value;
    }

    template<typename T, class alloc>
    collection<T, alloc> collection<T, alloc>::operator+(T element) {
        collection <T, alloc> result;
        result.add_all(*this).add(element);
        return result;
    }

    template<typename T, class alloc>
    collection<T, alloc>& collection<T, alloc>::add_all(collection<T, alloc> another) {
        for (collection<T, alloc>::iterator i = another.begin(); i < another.end(); i++) {
            add(another[i]);
        }
    }

    template<typename T, class alloc>
    typename collection<T, alloc>::size_type
    collection<T, alloc>::size() const {
        return length;
    }

    template<typename T, class alloc>
    typename collection<T, alloc>::iterator collection<T, alloc>::begin() {
        return collection::iterator(0, this);
    }

    template<typename T, class alloc>
    typename collection<T, alloc>::iterator collection<T, alloc>::end() {
        return collection::iterator(length, this);
    }

    template<typename T, class alloc>
    collection<T, alloc>::collection(collection::size_type length, T (*func)(int)) {
        init();
        preallocate(length);
        for (size_type i = 0; i < length; i++) {
            add(func(i));
        }
    }

    template<typename T, class alloc>
    collection<T, alloc>& collection<T, alloc>::remove(
            typename collection<T, alloc>::size_type index) {
        return *this;
    }

    template<typename T, class alloc>
    collection<T, alloc>& collection<T, alloc>::preallocate(collection::size_type count) {
        allocated_length += count;
        T **new_storage = new pointer[allocated_length];
        std::copy(element_storage, element_storage + length, new_storage);

        element_storage = new_storage;

        return *this;
    }

    template<typename T, class alloc>
    collection<T, alloc>& collection<T, alloc>::set_buffer_size(const collection::size_type& buffer_size) {
        this->buffer_size = buffer_size;
        return *this;
    }

    template<typename T, class alloc>
    typename collection<T, alloc>::size_type collection<T, alloc>::get_buffer_size() {
        return buffer_size;
    }

    template<typename T, class alloc>
    collection<T, alloc>::collection(collection::size_type length, T val) {
        init();
        preallocate(length);
        this->length = length;
        for (size_type i = 0; i < length; i++) {
            T* ptr = allocator.allocate(1);
            *ptr = val;
            element_storage[i] = ptr;
        }
    }

    template<typename T, class alloc>
    const char *collection<T, alloc>::index_out_of_bounds::what() const throw() {
        std::stringstream stringstream;
        stringstream << "Array length: " << length << ", required index: " << i;
        return stringstream.str().c_str();
    }

    template<typename T, class alloc>
    collection<T, alloc>::index_out_of_bounds::index_out_of_bounds(collection::size_type i,
                                                                   collection::size_type length)
            :i(i), length(length) {}

    template<typename T, class alloc>
    bool collection<T, alloc>::iterator::operator<(const collection::iterator &rhs) const {
        return i < rhs.i;
    }

    template<typename T, class alloc>
    bool collection<T, alloc>::iterator::operator>(const collection::iterator &rhs) const {
        return i > rhs.i;
    }

    template<typename T, class alloc>
    bool collection<T, alloc>::iterator::operator<=(const collection::iterator &rhs) const {
        return i <= rhs.i;
    }

    template<typename T, class alloc>
    bool collection<T, alloc>::iterator::operator>=(const collection::iterator &rhs) const {
        return i >= rhs.i;
    }

    template<typename T, class alloc>
    collection<T, alloc>::iterator::iterator(collection::size_type i, collection *outer)
            :i(i), outer(outer) {}

    template<typename T, class alloc>
    bool collection<T, alloc>::iterator::operator==(const collection::iterator &rhs) const {
        return i == rhs.i;
    }

    template<typename T, class alloc>
    bool collection<T, alloc>::iterator::operator!=(const collection::iterator &rhs) const {
        return !(rhs == *this);
    }

    template<typename T, class alloc>
    typename collection<T, alloc>::iterator collection<T, alloc>::iterator::operator+(int i) {
        return collection::iterator(this->i + i, outer);
    }

    template<typename T, class alloc>
    typename collection<T, alloc>::iterator collection<T, alloc>::iterator::operator-(int i) {
        return collection::iterator(this->i - i, outer);
    }

    template<typename T, class alloc>
    typename collection<T, alloc>::iterator collection<T, alloc>::iterator::operator++() {
        i++;
        return *this;
    }

    template<typename T, class alloc>
    typename collection<T, alloc>::iterator collection<T, alloc>::iterator::operator--() {
        i--;
        return *this;
    }

    template<typename T, class alloc>
    typename collection<T, alloc>::iterator collection<T, alloc>::iterator::operator++(int) {
        typename collection<T, alloc>::iterator &save = *this;
        i++;
        return save;
    }

    template<typename T, class alloc>
    typename collection<T, alloc>::iterator collection<T, alloc>::iterator::operator--(int) {
        typename collection<T, alloc>::iterator &save = *this;
        i++;
        return save;
    }

    template<typename T, class alloc>
    T &collection<T, alloc>::iterator::operator*() {
        return outer->get(i);
    }

    template <typename T = long long int> class fenwick_tree {
    public:
        typedef typename std::enable_if<std::is_integral<T>::value || std::is_floating_point<T>::value || std::is_same<T, libs::bigint>::value, long long>::type size_type;
    private:
        collection<T> elements;
        size_type _k, _2k, length;

        size_type f(size_type n) {
            return n - (n & (n - 1));
        }

        size_type get_k(size_type n) {
            size_type num = 1;
            size_type k = 0;
            while (num < n) {
                num <<= 1;
                k++;
            }
            return k;
        }

        size_type get_2k(size_type n) {
            size_type num = 1;
            while (num < n) {
                num <<= 1;
            }
            return num;
        }

        void init_k(size_type n) {
            size_type num = 1;
            size_type k = 0;
            while (num < n) {
                num <<= 1;
                k++;
            }
            _k = k;
            _2k = num;
            length = n;
        }

        inline void check_size(size_type n) {
            if (n < 0 || n >= length) throw index_out_of_bounds(n, length);
        }

        void init(int length) {
            init_k(length);
            elements = collection<T>(_2k, (T)0);
        }
    public:
        class index_out_of_bounds: std::exception {
        private:
            size_type i, length;
        public:
            index_out_of_bounds(size_type i, size_type length) : i(i), length(length) {}

            const char* what() const throw() {
                std::stringstream ss;
                ss << "Array length: " << length << ", requested index: " << i;
                return ss.str().c_str();
            }
        };

        fenwick_tree(const collection<T> &values) {
            init(values.size());
            elements[0] = values[0];
            for (size_type i = 1; i < values.size(); i++) {
                elements[i] = elements[i - 1] + values[i];
            }
            for (size_type i = values.size() - 1; i > 0; i--) {
                int lower_i = (i & (i+1)) - 1;
                if (lower_i >= 0) elements[i] -= elements[lower_i];
            }
        }

        fenwick_tree(int length) {
            init(length);
        }

        fenwick_tree& modify(size_type n, T delta) {
            check_size(n);
            for (size_type i = n; i < _2k; i += f(i + 1)) {
                elements[i] = elements[i] + delta;
            }
            return *this;
        }

        fenwick_tree& set(size_type n, T value) {
            check_size(n);
            modify(n, value - get_element(n));
            return *this;
        }

        // exclusive
        T count(size_type n) {
            check_size(n);
            T res = 0;
            for (size_type i = n - 1; i >= 0; i -= f(i + 1)) {
                res += elements[i];
            }
            return res;
        }

        // exclusive
        T count(size_type start, size_type end) {
            //check_size(start - 1);
            T diff = start > 0 ? count(start - 1) : 0;
            check_size(end - 1);
            if (start >= length) throw index_out_of_bounds(start, length);
            return count(end) - diff;
        }

        T get_element(size_type n) {
            return count(n, n + 1);
        }
    };

    /*template <typename ...Args> class size_calculator;

    template <typename T, typename ...Args> class size_calculator<T, Args...> {
    public:
        static constexpr int get_size() {
            return sizeof(T) + size_calculator<Args...>::get_size();
        }
    };

    template <> class size_calculator<> {
    public:
        static constexpr int get_size() {
            return 0;
        }
    };

    class c_dll_importer {
    private:
        void* handle;
        template <typename Return, typename ...Args>
        std::string generate_c_name(const std::string& name) {
            std::stringstream ss;
            ss << name << '@' << size_calculator<Args...>::get_size();
            return ss.str();
        };
    public:
        class lib_not_found_exception: std::exception {
        private:
            std::string name;
        public:
            lib_not_found_exception(const std::string &name) : name(name) {}
            const char* what() const throw() {
                std::stringstream ss;
                ss << "DLL named \"" << name << "\" was not found";
                return ss.str().c_str();
            }
            virtual ~lib_not_found_exception() throw() {}
        };
        class func_not_found_exception: std::exception {
        private:
            std::string name;
        public:
            func_not_found_exception(const std::string &name) : name(name) {}
            const char* what() const throw() {
                std::stringstream ss;
                ss << "Func named \"" << name << "\" was not found";
                return ss.str().c_str();
            }
            virtual ~func_not_found_exception() throw() {}
        };

        c_dll_importer(const std::string&);

        template <typename Return, typename ...Args>
        typename function<Return, Args...>::ptr_stdcall
        import_function(const std::string&);
    };*/

    /*template <int i, typename ...Args> class __tuple_getter;

    template <typename ...Args> class tuple;
    template <typename T, typename ...Args> class tuple<T, Args...> : tuple<Args...> {
    private:
        static constexpr int length = tuple<Args...>::length;
        T* head;
        friend __tuple_getter<length - 1, T, Args...>;
    public:
        tuple(const T &head, Args... args) : tuple(args...) {
            this->head = new T;
            *(this->head) = std::move(head);
        }
    };
    template <typename T> class tuple<T> {
    private:
        static constexpr int length = 1;
        T* head;
        friend __tuple_getter<0, T>;
    public:
        tuple(const T &head) {
            this->head = new T;
            *(this->head) = std::move(head);
        }
    };

    template <int i, typename T, typename ...Args> class __tuple_getter<i, T, Args...> {
    public:
        typedef typename __tuple_getter<i - 1, T, Args...>::return_type return_type;
        static return_type get(tuple<T, Args...> t) {
            return __tuple_getter<i - 1, T, Args...>::get(t);
        }
    };
    template <typename T, typename ...Args> class __tuple_getter<0, T, Args...> {
    public:
        typedef T& return_type;
        static return_type get(tuple<T, Args...> t) {
            return *(t.head);
        }
    };

    template <int i, typename T, typename ...Args>
    typename __tuple_getter<i, T, Args...>::return_type
    get_tuple(tuple<T, Args...> t) {
        return __tuple_getter<i, T, Args...>::get(t);
    }*/
}

/*#if defined(WINDOWS)
libs::c_dll_importer::c_dll_importer(const std::string& dll_name) {
    handle = new HINSTANCE[1];
    *((HINSTANCE*&)(handle)) = LoadLibrary(dll_name.c_str());
    if ((*((HINSTANCE*)(handle)))->i == 0) throw lib_not_found_exception(dll_name);
}
template <typename Return, typename ...Args>
typename libs::function<Return, Args...>::ptr_stdcall
libs::c_dll_importer::import_function(const std::string& name) {
    auto func = (typename libs::function<Return, Args...>::ptr_stdcall)
    GetProcAddress(*((HINSTANCE*) handle), generate_c_name<Return, Args...>(name).c_str());
    if (func == 0) throw func_not_found_exception(name);
    return func;
}
#elif defined(LINUX)
libs::c_dll_importer::c_dll_importer(std::string dll_name) {
    handle = dlopen(dll_name.c_str(), RTLD_LAZY);
    if (handle == 0) throw lib_not_found_exception(dll_name);
}
template <typename Return, typename ...Args>
typename libs::function<Return, Args...>::ptr_stdcall
libs::c_dll_importer::import_function(const std::string& name) {
    auto func = (typename libs::function<Return, Args...>::ptr_stdcall)
    dlsym(handle, generate_c_name<Return, Args...>(name).c_str());
    if (func == 0) throw func_not_found_exception(name);
    return func;
}
#endif*/