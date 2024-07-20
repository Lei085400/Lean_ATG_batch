["have n_pos : 0 < n := by linarith", "have : 1 \u2264 n := by linarith", "have h1 : 1 \u2264 1 := by linarith", "have : 1 \u2264 2 := by linarith", "norm_num"]
"n : \u2115\nh : 2 \u2264 n\nn_pos : 0 < n\nthis\u271d : 1 \u2264 n\nh1 : 1 \u2264 1\nthis : 1 \u2264 2\n\u22a2 \u2211 k in Ico 1 (n + 1), k ^ 2 * Nat.choose n k = n * ((n - 1) * 2 ^ (n - 2) + 2 ^ (n - 1))"

["rw [cast_sum (range (n+1)) fun x => x * Nat.choose (2 * n) x]"]
"n : \u2115\n\u22a2 \u2211 k in range (n + 1), \u2191n * \u2191(Nat.choose (2 * n) k) - \u2211 x in range (n + 1), \u2191(x * Nat.choose (2 * n) x) =\n    \u2191(\u2211 k in range (n + 1), n * Nat.choose (2 * n) k) - \u2211 x in range (n + 1), \u2191(x * Nat.choose (2 * n) x)"

["rw [cast_sum, cast_sum]"]
"n : \u2115\n\u22a2 \u2211 k in range (n + 1), \u2191n * \u2191(Nat.choose (2 * n) k) - \u2211 x in range (n + 1), \u2191(x * Nat.choose (2 * n) x) =\n    \u2211 x in range (n + 1), \u2191(n * Nat.choose (2 * n) x) - \u2211 x in range (n + 1), \u2191(x * Nat.choose (2 * n) x)"

["rw [Finset.sum_range_add]"]
"n : \u2115\n\u22a2 2 ^ (2 * n) =\n    \u2211 x in range n, Nat.choose (2 * n) x + \u2211 x in range 1, Nat.choose (2 * n) (n + x) +\n      \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]"]
"n : \u2115\n\u22a2 (2 ^ 2) ^ n = \u2211 k in range (n + 1), Nat.choose (2 * n) k + \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]"]
"n : \u2115\n\u22a2 (2 * 2) ^ n = \u2211 k in range (n + 1), Nat.choose (2 * n) k + \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "simp only [Nat.pow_succ, Nat.pow_one]"]
"n : \u2115\n\u22a2 (2 ^ 0 * 2 * 2) ^ n =\n    \u2211 k in range (n + 1), Nat.choose (2 * n) k + \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw [Finset.sum_range_add]"]
"n : \u2115\n\u22a2 (2 ^ 2) ^ n =\n    \u2211 x in range n, Nat.choose (2 * n) x + \u2211 x in range 1, Nat.choose (2 * n) (n + x) +\n      \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw[Nat.pow_succ]"]
"n : \u2115\n\u22a2 (2 ^ 1 * 2) ^ n = \u2211 k in range (n + 1), Nat.choose (2 * n) k + \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]", "rw [Finset.sum_range_add]"]
"n : \u2115\n\u22a2 (2 * 2) ^ n =\n    \u2211 x in range n, Nat.choose (2 * n) x + \u2211 x in range 1, Nat.choose (2 * n) (n + x) +\n      \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]", "simp only [mul_pow]"]
"n : \u2115\n\u22a2 2 ^ n * 2 ^ n = \u2211 k in range (n + 1), Nat.choose (2 * n) k + \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]", "rw [Finset.sum_range_add]", "rw [mul_pow]"]
"n : \u2115\n\u22a2 2 ^ n * 2 ^ n =\n    \u2211 x in range n, Nat.choose (2 * n) x + \u2211 x in range 1, Nat.choose (2 * n) (n + x) +\n      \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]", "rw [Finset.sum_range_add]", "simp only [mul_pow]"]
"n : \u2115\n\u22a2 2 ^ n * 2 ^ n =\n    \u2211 x in range n, Nat.choose (2 * n) x + \u2211 x in range 1, Nat.choose (2 * n) (n + x) +\n      \u2211 x in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) x"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]", "rw [Finset.sum_range_add]", "simp"]
"n : \u2115\n\u22a2 (2 * 2) ^ n =\n    \u2211 x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n + \u2211 x in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) x"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]", "rw [Finset.sum_range_add]", "simp", "rw [mul_pow]"]
"n : \u2115\n\u22a2 2 ^ n * 2 ^ n =\n    \u2211 x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n + \u2211 x in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) x"
["rw [cast_sum (range (n+1)) fun x => x * Nat.choose (2 * n) x]"]
"n : \u2115\n\u22a2 \u2211 k in range (n + 1), \u2191n * \u2191(Nat.choose (2 * n) k) - \u2211 x in range (n + 1), \u2191(x * Nat.choose (2 * n) x) =\n    \u2191(\u2211 k in range (n + 1), n * Nat.choose (2 * n) k) - \u2211 x in range (n + 1), \u2191(x * Nat.choose (2 * n) x)"

["rw [cast_sum, cast_sum]"]
"n : \u2115\n\u22a2 \u2211 k in range (n + 1), \u2191n * \u2191(Nat.choose (2 * n) k) - \u2211 x in range (n + 1), \u2191(x * Nat.choose (2 * n) x) =\n    \u2211 x in range (n + 1), \u2191(n * Nat.choose (2 * n) x) - \u2211 x in range (n + 1), \u2191(x * Nat.choose (2 * n) x)"

["rw [Finset.sum_range_add]"]
"n : \u2115\n\u22a2 2 ^ (2 * n) =\n    \u2211 x in range n, Nat.choose (2 * n) x + \u2211 x in range 1, Nat.choose (2 * n) (n + x) +\n      \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]"]
"n : \u2115\n\u22a2 (2 ^ 2) ^ n = \u2211 k in range (n + 1), Nat.choose (2 * n) k + \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]"]
"n : \u2115\n\u22a2 (2 * 2) ^ n = \u2211 k in range (n + 1), Nat.choose (2 * n) k + \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "simp only [Nat.pow_succ, Nat.pow_one]"]
"n : \u2115\n\u22a2 (2 ^ 0 * 2 * 2) ^ n =\n    \u2211 k in range (n + 1), Nat.choose (2 * n) k + \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw [Finset.sum_range_add]"]
"n : \u2115\n\u22a2 (2 ^ 2) ^ n =\n    \u2211 x in range n, Nat.choose (2 * n) x + \u2211 x in range 1, Nat.choose (2 * n) (n + x) +\n      \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw[Nat.pow_succ]"]
"n : \u2115\n\u22a2 (2 ^ 1 * 2) ^ n = \u2211 k in range (n + 1), Nat.choose (2 * n) k + \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]", "rw [Finset.sum_range_add]"]
"n : \u2115\n\u22a2 (2 * 2) ^ n =\n    \u2211 x in range n, Nat.choose (2 * n) x + \u2211 x in range 1, Nat.choose (2 * n) (n + x) +\n      \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]", "simp only [mul_pow]"]
"n : \u2115\n\u22a2 2 ^ n * 2 ^ n = \u2211 k in range (n + 1), Nat.choose (2 * n) k + \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]", "rw [Finset.sum_range_add]", "rw [mul_pow]"]
"n : \u2115\n\u22a2 2 ^ n * 2 ^ n =\n    \u2211 x in range n, Nat.choose (2 * n) x + \u2211 x in range 1, Nat.choose (2 * n) (n + x) +\n      \u2211 k in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) k"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]", "rw [Finset.sum_range_add]", "simp only [mul_pow]"]
"n : \u2115\n\u22a2 2 ^ n * 2 ^ n =\n    \u2211 x in range n, Nat.choose (2 * n) x + \u2211 x in range 1, Nat.choose (2 * n) (n + x) +\n      \u2211 x in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) x"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]", "rw [Finset.sum_range_add]", "simp"]
"n : \u2115\n\u22a2 (2 * 2) ^ n =\n    \u2211 x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n + \u2211 x in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) x"

["rw[Nat.pow_mul]", "rw [Nat.pow_succ, Nat.pow_one]", "rw [Finset.sum_range_add]", "simp", "rw [mul_pow]"]
"n : \u2115\n\u22a2 2 ^ n * 2 ^ n =\n    \u2211 x in range n, Nat.choose (2 * n) x + Nat.choose (2 * n) n + \u2211 x in Ico (n + 1) (2 * n + 1), Nat.choose (2 * n) x"

["rw [mul_comm]"]
"n : \u2115\nh : 1 \u2264 n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) * \u2191n = \u2191n * \u2191(Nat.choose (2 * n - 1) n)"

["rw [mul_div]"]
"n : \u2115\nh : 1 \u2264 n\n\u22a2 \u2191n * \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191n * \u2191(Nat.choose (2 * n - 1) n)"

["simp"]
"n : \u2115\nh : 1 \u2264 n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191(Nat.choose (2 * n - 1) n) \u2228 n = 0"

["push_cast"]
"n : \u2115\nh : 1 \u2264 n\n\u22a2 \u2191n * (\u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!)) = \u2191n * \u2191(Nat.choose (2 * n - 1) n)"

["norm_cast"]
"n : \u2115\nh : 1 \u2264 n\n\u22a2 \u2191n * (\u2191(2 * n - 1)! / \u2191(n ! * (n - 1)!)) = \u2191(n * Nat.choose (2 * n - 1) n)"

["norm_cast", "rw [cast_mul]"]
"n : \u2115\nh : 1 \u2264 n\n\u22a2 \u2191n * (\u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!)) = \u2191(n * Nat.choose (2 * n - 1) n)"

["simp", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh : 1 \u2264 n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh : 1 \u2264 n\n\u22a2 n \u2264 2 * n - 1"

["simp", "rw [mul_comm]"]
"n : \u2115\nh : 1 \u2264 n\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191(Nat.choose (n * 2 - 1) n) \u2228 n = 0"

["simp", "rw [mul_comm]", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh : 1 \u2264 n\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh : 1 \u2264 n\n\u22a2 n \u2264 n * 2 - 1"

["simp", "have : 1 \u2264 2 * n := by linarith", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 2 * n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 2 * n\n\u22a2 n \u2264 2 * n - 1"

["simp", "have : 1 \u2264 n := by linarith", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh this : 1 \u2264 n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh this : 1 \u2264 n\n\u22a2 n \u2264 2 * n - 1"

["norm_cast", "rw [mul_comm]"]
"n : \u2115\nh : 1 \u2264 n\n\u22a2 \u2191(2 * n - 1)! / \u2191(n ! * (n - 1)!) * \u2191n = \u2191(n * Nat.choose (2 * n - 1) n)"

["simp", "have : 1 \u2264 2 * n := by linarith", "rw [mul_comm]"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 2 * n\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191(Nat.choose (n * 2 - 1) n) \u2228 n = 0"

["simp", "have : 1 \u2264 2 * n := by linarith", "norm_cast"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 2 * n\n\u22a2 \u2191(2 * n - 1)! / \u2191(n ! * (n - 1)!) = \u2191(Nat.choose (2 * n - 1) n) \u2228 n = 0"

["simp", "have : 1 \u2264 2 * n := by linarith", "have : 1 \u2264 2 * n := by linarith", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 2 * n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 2 * n\n\u22a2 n \u2264 2 * n - 1"

["simp", "have : 1 \u2264 2 * n := by linarith", "rw [mul_comm]", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 2 * n\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 2 * n\n\u22a2 n \u2264 n * 2 - 1"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 n * 2\n\u22a2 n \u2264 n * 2 - 1"

["simp", "have n_pos : 0 < n := by linarith", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh : 1 \u2264 n\nn_pos : 0 < n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh : 1 \u2264 n\nn_pos : 0 < n\n\u22a2 n \u2264 2 * n - 1"

["simp", "rw [mul_comm]", "have : 1 \u2264 n := by linarith", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh this : 1 \u2264 n\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh this : 1 \u2264 n\n\u22a2 n \u2264 n * 2 - 1"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "rw [mul_comm]"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 n * 2\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191(Nat.choose (2 * n - 1) n) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "norm_cast"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / \u2191(n ! * (n - 1)!) = \u2191(Nat.choose (n * 2 - 1) n) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 n \u2264 n * 2 - 1"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "rw [mul_comm]"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191(Nat.choose (2 * n - 1) n) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "rw [mul_comm] at this"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d : 1 \u2264 n * 2\nthis : 1 \u2264 2 * n\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191(Nat.choose (n * 2 - 1) n) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "norm_cast"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / \u2191(n ! * (n - 1)!) = \u2191(Nat.choose (n * 2 - 1) n) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "norm_cast", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / \u2191(n ! * (n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 n \u2264 n * 2 - 1"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "have : 2 \u2264 n * 2 := by linarith", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 2 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 2 \u2264 n * 2\n\u22a2 n \u2264 n * 2 - 1"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "have : 2 \u2264 n * 2 := by linarith", "rw [mul_comm]"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 2 \u2264 n * 2\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191(Nat.choose (2 * n - 1) n) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n := by linarith", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 1 \u2264 n\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 1 \u2264 n\n\u22a2 n \u2264 n * 2 - 1"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "rw [mul_comm]", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 n \u2264 2 * n - 1"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n := by linarith", "rw [mul_comm]"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 1 \u2264 n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191(Nat.choose (2 * n - 1) n) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "have : 2 \u2264 n * 2 := by linarith", "norm_cast"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 2 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / \u2191(n ! * (n - 1)!) = \u2191(Nat.choose (n * 2 - 1) n) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "have : 2 \u2264 n * 2 := by linarith", "field_simp"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 2 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! = \u2191(Nat.choose (n * 2 - 1) n) * (\u2191n ! * \u2191(n - 1)!) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "have : 2 \u2264 n * 2 := by linarith", "norm_num"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 2 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191(Nat.choose (n * 2 - 1) n) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "rw [mul_comm]", "rw [choose_eq_factorial_div_factorial]"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 n * 2\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0\n\nn : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 n * 2\n\u22a2 n \u2264 2 * n - 1"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 n * 2\n\u22a2 n \u2264 n * 2 - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 n \u2264 n * 2 - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0"

["simp", "have : 1 \u2264 2 * n := by linarith", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 2 * n\n\u22a2 n \u2264 2 * n - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 2 * n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "have : 2 \u2264 n * 2 := by linarith", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 2 \u2264 n * 2\n\u22a2 n \u2264 n * 2 - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 2 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "have : 2 \u2264 n * 2 := by linarith", "rw [choose_eq_factorial_div_factorial]", "have : 1 \u2264 n * 2 := by linarith", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 2 \u2264 n * 2\n\u22a2 n \u2264 n * 2 - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b2 this\u271d\u00b9 : 1 \u2264 n * 2\nthis\u271d : 2 \u2264 n * 2\nthis : 1 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n := by linarith", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 1 \u2264 n\n\u22a2 n \u2264 n * 2 - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d : 1 \u2264 n * 2\nthis : 1 \u2264 n\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "rw [choose_eq_factorial_div_factorial]", "have : 1 \u2264 n * 2 := by linarith", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 n \u2264 n * 2 - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d\u00b9 this\u271d this : 1 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0"

["simp", "have : 1 \u2264 2 * n := by linarith", "rw [choose_eq_factorial_div_factorial]", "have : 1 \u2264 2 * n := by linarith", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 2 * n\n\u22a2 n \u2264 2 * n - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 2 * n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "rw [mul_comm]", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 n \u2264 2 * n - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "have : 1 \u2264 n * 2 := by linarith", "norm_cast", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 n \u2264 n * 2 - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / \u2191(n ! * (n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0"

["simp", "have : 1 \u2264 2 * n := by linarith", "have : 1 \u2264 2 * n := by linarith", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 2 * n\n\u22a2 n \u2264 2 * n - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 2 * n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "rw [choose_eq_factorial_div_factorial]", "have : 1 \u2264 n * 2 := by linarith", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 n * 2\n\u22a2 n \u2264 n * 2 - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis\u271d this : 1 \u2264 n * 2\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n * 2 := by linarith", "rw [mul_comm]", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 n * 2\n\u22a2 n \u2264 2 * n - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 n * 2\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0"

["simp", "have : 1 \u2264 2 * n := by linarith", "rw [mul_comm]", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 2 * n\n\u22a2 n \u2264 n * 2 - 1\n\nn : \u2115\nh : 1 \u2264 n\nthis : 1 \u2264 2 * n\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0"

["simp", "rw [mul_comm]", "have : 1 \u2264 n := by linarith", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh this : 1 \u2264 n\n\u22a2 n \u2264 n * 2 - 1\n\nn : \u2115\nh this : 1 \u2264 n\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0"

["simp", "rw [mul_comm]", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh : 1 \u2264 n\n\u22a2 n \u2264 n * 2 - 1\n\nn : \u2115\nh : 1 \u2264 n\n\u22a2 \u2191(n * 2 - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((n * 2 - 1)! / (n ! * (n * 2 - 1 - n)!)) \u2228 n = 0"

["simp", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh : 1 \u2264 n\n\u22a2 n \u2264 2 * n - 1\n\nn : \u2115\nh : 1 \u2264 n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0"

["simp", "have n_pos : 0 < n := by linarith", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh : 1 \u2264 n\nn_pos : 0 < n\n\u22a2 n \u2264 2 * n - 1\n\nn : \u2115\nh : 1 \u2264 n\nn_pos : 0 < n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0"

["simp", "have : 1 \u2264 n := by linarith", "rw [choose_eq_factorial_div_factorial]", "swap"]
"n : \u2115\nh this : 1 \u2264 n\n\u22a2 n \u2264 2 * n - 1\n\nn : \u2115\nh this : 1 \u2264 n\n\u22a2 \u2191(2 * n - 1)! / (\u2191n ! * \u2191(n - 1)!) = \u2191((2 * n - 1)! / (n ! * (2 * n - 1 - n)!)) \u2228 n = 0"

["rw [div_eq_mul_inv]"]
"G : Type u_1\ninst\u271d : DivInvMonoid G\na\u271d b\u271d c a b : G\n\u22a2 a * (b * a)\u207b\u00b9 = b\u207b\u00b9"

["rw [div_eq_mul_inv, div_eq_mul_inv]"]
"G : Type u_1\ninst\u271d : DivInvMonoid G\na\u271d b\u271d c\u271d a b c : G\n\u22a2 a * b * c\u207b\u00b9 = a * (b * c\u207b\u00b9)"

["rw [div_eq_mul_inv]"]
"G : Type u_1\ninst\u271d : DivInvMonoid G\na b c x : G\n\u22a2 x\u207b\u00b9 = 1 * x\u207b\u00b9"

["rw [div_eq_mul_inv, div_eq_mul_inv]"]
"G : Type u_1\ninst\u271d : DivInvMonoid G\na b c : G\n\u22a2 b * a\u207b\u00b9 = c * a\u207b\u00b9 \u2194 b = c"

["rw [div_eq_mul_inv]"]
"G : Type u_1\ninst\u271d : DivInvMonoid G\na b c : G\n\u22a2 b * a\u207b\u00b9 = c / a \u2194 b = c"

["rw [div_eq_mul_inv, div_eq_mul_inv, eq_comm]"]
"G : Type u_1\ninst\u271d : DivInvMonoid G\na b c : G\n\u22a2 c * a\u207b\u00b9 = b * a\u207b\u00b9 \u2194 b = c"

["rw [div_eq_mul_inv]", "rw [\u2190 div_eq_mul_inv]"]
"G : Type u_1\ninst\u271d : DivInvMonoid G\na b c : G\n\u22a2 b / a = c / a \u2194 b = c"

["rw [div_eq_mul_inv, div_eq_mul_inv, mul_left_comm]"]
"G : Type u_1\ninst\u271d : DivInvMonoid G\na\u271d b\u271d c a b : G\n\u22a2 a / (b * a) = b\u207b\u00b9"

