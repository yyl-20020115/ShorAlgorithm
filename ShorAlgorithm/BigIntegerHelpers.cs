using System.Numerics;
using System.Reflection;
using System.Security.Cryptography;

namespace ShorAlgorithm;

public static class BigIntegerHelpers
{
    /*********************************************************************
     *	shor.cc -- Use Shor's Algorithm
     *		to factor a large BigInteger
     * ChangeLog:
     *  970225 -- Created by Paul Herman <a540pau@pslc.ucla.edu>
    **********************************************************************/
    public static BigInteger GenerateRandomOddBigInteger(int count = 8)
    {
        if (count <= 0) throw new ArgumentException(null, nameof(count));
        // 创建一个RandomNumberGenerator实例
        using var generator = RandomNumberGenerator.Create();
        // 生成一个足够长的字节数组，例如16字节（128位）
        var randomBytes = new byte[count]; // 可以根据需要增加字节数以生成更大的数
        generator.GetBytes(randomBytes);
        randomBytes[0] |= 1; // 确保生成的数是奇数，以增加找到因子的概率
                             // 将字节数组转换为BigInteger
                             // 注意：这里使用了BigEndianBitConverter，因为BigInteger期望高位在前（大端格式）
        randomBytes[^1] &= 0x7f; // 确保生成的数是正数
        return new(randomBytes);
    }
    public static bool IsPrime(BigInteger number)
    {
        // 小于等于1的数不是质数
        if (number <= 1)
            return false;

        // 2 是质数
        if (number == 2)
            return true;

        // 偶数（除了2）不是质数
        if (number.IsEven)
            return false;

        // 使用试除法检查从3到√n的所有奇数
        BigInteger sqrt = Sqrt(number);
        for (BigInteger i = 3; i <= sqrt; i += 2)
        {
            if (number % i == 0)
                return false;
        }

        return true;
    }

    // 计算 BigInteger 的平方根
    public static BigInteger Sqrt(BigInteger number)
    {
        if (number == 0)
            return 0;

        BigInteger x = number;
        BigInteger y = (x + 1) / 2;

        while (y < x)
        {
            x = y;
            y = (x + number / x) / 2;
        }

        return x;
    }
    public static long GetCycle(BigInteger a, BigInteger n)
    {
        var count = 1L;

        Parallel.For(1L, long.MaxValue, (i, state) =>
        {
            if (BigInteger.ModPow(a, i, n) == BigInteger.One)
            {
                count = i;
                state.Stop();
            }
        });

        return count;
    }
    public static long GetCycle(BigInteger n, long d = 3)
    {
        var count = 1L;
        BigInteger a = GenerateRandomOddBigInteger(n.GetByteCount());
        Parallel.For(1L, long.MaxValue, (i, state) =>
        {
            if (BigInteger.ModPow(a, i, n) == BigInteger.One)
            {
                count = i;
                state.Stop();
            }
        });

        return count;
    }
    public static BigInteger Pow(BigInteger a, BigInteger b)
    {
        const int max = int.MaxValue >> 1;
        var total = BigInteger.One;
        while (b > max)
        {
            b -= max;
            total *= BigInteger.Pow(a, max);
        }
        return total *= BigInteger.Pow(a, (int)b);
    }

    public static BigInteger ShorFactor(BigInteger n, BigInteger a, long retries = 4096, bool use_cycle = false)
    {
        BigInteger t1, t2, f1, f2, r;
        int j;

        a = a.IsZero ? GenerateRandomOddBigInteger(n.GetByteCount()) : a;

        while (true)
        {
            j = 2;
            //我在这里改为随机化

            r = use_cycle ? GetCycle(a, n) : BigInteger.ModPow(a, j, n);
            for (; ; j += 2)
            {
                //随机数a是n的因子
                f1 = BigInteger.GreatestCommonDivisor(a, n);
                if (f1 == n) goto tail;
                if (f1 != BigInteger.One) return f1;
                //t1和t2分别是a^((a^j mod n)/2) mod n的+1和-1
                t1 = BigInteger.ModPow(a, (r >> 1), n);
                t1 += 1;
                t2 = t1 - 2;

                //t1=(a^(r/2) mod n) + 1
                //t2=(a^(r/2) mod n) - 1

                //测试t1
                f1 = BigInteger.GreatestCommonDivisor(t1, n);
                if (f1 != BigInteger.One && f1 != n)
                    return f1;
                //测试t2
                f2 = BigInteger.GreatestCommonDivisor(t2, n);
                if (f2 != BigInteger.One && f2 != n)
                    return f2;
                //如果t1和t2都没有找到因子，那么就换一个a继续试s
                a++;
                if (--retries == 0)
                    return n;
                //计算a^j mod n,求r的下一个数值
                r = BigInteger.ModPow(a, j, n);
                //如果r为负数，说明a^j mod n的结果是负数，这不应该发生，因为模运算的结果应该在0到n-1之间
                if (r < 0) goto tail;
            }
        tail:
            a = BigIntegerHelpers.GenerateRandomOddBigInteger(n.GetByteCount());
        }
    }

    public static bool IsInteger(double value)
        => Math.Abs(value - (int)value) < double.Epsilon
        ;

    public static (BigInteger, BigInteger) Log(BigInteger a, BigInteger n)
    {
        if (a > n)
        {
            return (BigInteger.Zero, n);
        }
        var count = BigInteger.Zero;
        var result = BigInteger.One;
        while (true)
        {
            if (result > n)
                break;
            result *= a;
            count++;
        }

        return (count, n - result);
    }
    public static BigInteger GetFactor(BigInteger N, long kmax = 4096, long retries = 1024)
    {
        if (N.IsEven) return 2;
        //N is 2n+1
        for (var retry = 0L; retry < retries; retry++)
        {
            var a = GenerateRandomOddBigInteger(N.GetByteCount());
            for (var k = 1L; k <= kmax; k++)
            {
                for (var n = Sqrt(k * N); n >= 1; n >>= 1)
                {
                    var res = (k * N - n ^ 2);
                    (var s, var rem) = Log(a, res);
                    if (rem != 0 && s.IsEven) continue;
                    {
                        s >>= 1;
                        var t1 = Pow(a, s) - n;
                        var t2 = Pow(a, s) + n;
                        var f1 = BigInteger.GreatestCommonDivisor(t1, N);
                        if (f1 != BigInteger.One)
                            return t1;
                        var f2 = BigInteger.GreatestCommonDivisor(t2, N);
                        if (f2 != BigInteger.One)
                            return f2;
                    }
                }
            }
        }
        return BigInteger.One;
    }

}