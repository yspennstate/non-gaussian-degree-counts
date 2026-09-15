import Mathlib

/-!
Arithmetic behind the two offspring laws whose conditioned Galton-Watson trees have
non-Gaussian degree-one counts.

Subcritical law: `n_1 = 256`, `n_{r+1} = n_r^4`, `d_0 = 3/4`, `d_r = d_{r-1} (1 - 2 n_r^{-3})`,
`H_r = d_{r-1} n_r`, atoms `L_r^± = H_r ± sqrt(n_r)` of mass `p_r = n_r^{-4}`.
Certified here: the first two stages, the bounds `5/8 < d_r ≤ 3/4`, the total rare mass
`< 4/256^4`, at most one current atom and no later atom on the conditioning event, the exact
centering identity, the Bernstein exponent, and the zero of the limit characteristic function.

Critical law: the base law `(5/8, 1/4, 1/8)`, the mean update by `Δ_r/2 = 2^{-r-1}`, the
partial sums of the mean increments, and the first-stage atoms at `n_1 = 2^17`.
-/

namespace DegreeCounts

/-! ### The subcritical law -/

/-- Stage sizes `n_1 = 256`, `n_{r+1} = n_r^4` (index shifted: `nn 0 = n_1`). -/
def nn : ℕ → ℕ
  | 0 => 256
  | k + 1 => (nn k) ^ 4

/-- `d_0 = 3/4`, `d_{k+1} = d_k (1 - 2 / n_{k+1}^3)`. -/
def dd : ℕ → ℚ
  | 0 => 3 / 4
  | k + 1 => dd k * (1 - 2 / ((nn k : ℚ) ^ 3))

/-- Total mass of the rare atoms of the first `k` stages. -/
def mass : ℕ → ℚ
  | 0 => 0
  | k + 1 => mass k + 2 / ((nn k : ℚ) ^ 4)

theorem nn_ge (k : ℕ) : 256 ≤ nn k := by
  induction k with
  | zero => simp [nn]
  | succ k ih =>
    show 256 ≤ (nn k) ^ 4
    calc 256 ≤ nn k := ih
      _ ≤ (nn k) ^ 4 := Nat.le_self_pow (by norm_num) _

/-- Stage 1: `H_1 = 192`, `L_1^- = 176`, `L_1^+ = 208`. -/
theorem stage_one : dd 0 * (nn 0 : ℚ) = 192 ∧ (192 : ℚ) - 16 = 176 ∧ (192 : ℚ) + 16 = 208 := by
  simp [dd, nn]; norm_num

/-- Stage 2: `n_2 = 2^32`, `H_2 = 3221225088`, `L_2^± = H_2 ± 65536`. -/
theorem stage_two :
    (nn 1 : ℚ) = 2 ^ 32 ∧ dd 1 * (nn 1 : ℚ) = 3221225088 ∧
    (3221225088 : ℚ) - 65536 = 3221159552 ∧ (3221225088 : ℚ) + 65536 = 3221290624 := by
  simp [dd, nn]; norm_num

/-- The invariant `5/8 + 2/n_{k+1}^3 ≤ d_k`; in particular every `d_k` exceeds `5/8`. -/
theorem dd_lower (k : ℕ) : 5 / 8 + 2 / ((nn k : ℚ) ^ 3) ≤ dd k := by
  induction k with
  | zero => simp [dd, nn]; norm_num
  | succ k ih =>
    have hn : (256 : ℚ) ≤ nn k := by exact_mod_cast nn_ge k
    have hx0 : (0 : ℚ) < (nn k : ℚ) ^ 3 := by positivity
    set x : ℚ := 1 / ((nn k : ℚ) ^ 3) with hxdef
    have hxpos : 0 < x := by positivity
    have hxle : x ≤ 1 / 256 ^ 3 := by
      rw [hxdef]; apply one_div_le_one_div_of_le (by positivity); gcongr
    have hnext : (nn (k + 1) : ℚ) ^ 3 = ((nn k : ℚ) ^ 3) ^ 4 := by
      simp [nn]; ring
    have h2 : 2 / ((nn (k + 1) : ℚ) ^ 3) = 2 * x ^ 4 := by
      rw [hnext, hxdef]; field_simp
    have hd : dd (k + 1) = dd k * (1 - 2 * x) := by
      simp only [dd]; rw [hxdef]; ring
    have hih : 5 / 8 + 2 * x ≤ dd k := by
      have : 2 / ((nn k : ℚ) ^ 3) = 2 * x := by rw [hxdef]; ring
      linarith [ih, this]
    rw [h2, hd]
    have hpos : 0 < 1 - 2 * x := by nlinarith
    have hxs : x ≤ 1 / 16777216 := by norm_num at hxle; linarith
    nlinarith [mul_le_mul_of_nonneg_right hih hpos.le, hxpos, hxs,
      pow_pos hxpos 2, pow_pos hxpos 3, pow_pos hxpos 4]

theorem dd_pos_lt (k : ℕ) : 5 / 8 < dd k := by
  have := dd_lower k
  have : (0 : ℚ) < 2 / ((nn k : ℚ) ^ 3) := by
    have := nn_ge k; positivity
  linarith

theorem dd_le (k : ℕ) : dd k ≤ 3 / 4 := by
  induction k with
  | zero => simp [dd]
  | succ k ih =>
    have hn : (256 : ℚ) ≤ nn k := by exact_mod_cast nn_ge k
    have h0 : 0 < dd k := by linarith [dd_pos_lt k]
    have hx : 0 ≤ 2 / ((nn k : ℚ) ^ 3) := by positivity
    have hf : dd k * (1 - 2 / ((nn k : ℚ) ^ 3)) ≤ dd k := by nlinarith
    simpa [dd] using le_trans hf ih

/-- The invariant `mass k ≤ 4/256^4 - 4/n_{k+1}^4`; hence the rare mass stays below `4/256^4`. -/
theorem mass_upper (k : ℕ) : mass k ≤ 4 / 256 ^ 4 - 4 / ((nn k : ℚ) ^ 4) := by
  induction k with
  | zero => simp [mass, nn]
  | succ k ih =>
    have hn : (256 : ℚ) ≤ nn k := by exact_mod_cast nn_ge k
    have hx0 : (0 : ℚ) < (nn k : ℚ) ^ 4 := by positivity
    set y : ℚ := 1 / ((nn k : ℚ) ^ 4) with hydef
    have hypos : 0 < y := by positivity
    have hyle : y ≤ 1 / 256 ^ 4 := by
      rw [hydef]; apply one_div_le_one_div_of_le (by positivity); gcongr
    have hnext : (nn (k + 1) : ℚ) ^ 4 = ((nn k : ℚ) ^ 4) ^ 4 := by
      simp [nn]
    have h4 : 4 / ((nn (k + 1) : ℚ) ^ 4) = 4 * y ^ 4 := by
      rw [hnext, hydef]; field_simp
    have hm : mass (k + 1) = mass k + 2 * y := by
      simp only [mass]; rw [hydef]; ring
    have hih : mass k ≤ 4 / 256 ^ 4 - 4 * y := by
      have : 4 / ((nn k : ℚ) ^ 4) = 4 * y := by rw [hydef]; ring
      linarith [ih, this]
    rw [h4, hm]
    have hys : y ≤ 1 / 4294967296 := by norm_num at hyle; linarith
    nlinarith [pow_pos hypos 2, pow_pos hypos 3, pow_pos hypos 4, hys]

theorem mass_lt (k : ℕ) : mass k < 4 / 256 ^ 4 := by
  have := mass_upper k
  have : (0 : ℚ) < 4 / ((nn k : ℚ) ^ 4) := by
    have := nn_ge k; positivity
  linarith

/-- At most one current atom: `2 L^- > n - 1` when `L^- = d n - s`, `s = sqrt n ≥ 16`, `d ≥ 5/8`. -/
theorem one_current_atom (n s d : ℝ) (hs : s * s = n) (h16 : 16 ≤ s) (hd : 5 / 8 ≤ d) :
    n - 1 < 2 * (d * n - s) := by
  nlinarith

/-- No later atom: `L' = d' m - sqrt m > n` for `m = n^4` (so `sqrt m = n^2`), `n ≥ 2`, `d' ≥ 5/8`. -/
theorem no_later_atom (n d' : ℝ) (hn : 2 ≤ n) (hd : 5 / 8 ≤ d') :
    n < d' * n ^ 4 - n ^ 2 := by
  have h2 : 2 * n ≤ n ^ 2 := by nlinarith
  have hsq : 4 ≤ n ^ 2 := by nlinarith
  have h4 : 4 * n ^ 2 ≤ n ^ 4 := by nlinarith [hsq, sq_nonneg (n ^ 2)]
  have hd' : 5 / 8 * n ^ 4 ≤ d' * n ^ 4 :=
    mul_le_mul_of_nonneg_right hd (by positivity)
  linarith

/-- The exact centering identity: with `u = 1 - d`, `z = 1 - t`, `μ = u / z`,
`k = n - 1 - (d n + ε s)`, one has `k - (n-1) μ = -ε s - d - (n-1) u t / z`. -/
theorem centering (n d t s ε : ℝ) (hz : 1 - t ≠ 0) :
    (n - 1 - (d * n + ε * s)) - (n - 1) * ((1 - d) / (1 - t))
      = -ε * s - d - (n - 1) * (1 - d) * t / (1 - t) := by
  field_simp
  ring

/-- The Bernstein exponent: if `n/3 ≤ D ≤ n`, `0 ≤ V ≤ n` and `M ≥ 1`, then
`D^2 / (2 (V + M D / 3)) ≥ n / (24 M)`. -/
theorem bernstein_exponent (n D V M : ℝ) (hD1 : n / 3 ≤ D) (hD2 : D ≤ n) (hV0 : 0 ≤ V)
    (hV : V ≤ n) (hM : 1 ≤ M) (hn : 0 < n) :
    n / (24 * M) ≤ D ^ 2 / (2 * (V + M * D / 3)) := by
  have hden : 0 < 2 * (V + M * D / 3) := by nlinarith
  rw [div_le_div_iff₀ (by positivity) hden]
  nlinarith [mul_le_mul_of_nonneg_left hV (by linarith : (0:ℝ) ≤ M),
    mul_le_mul_of_nonneg_left hD2 (by linarith : (0:ℝ) ≤ M), sq_nonneg (D - n / 3)]

/-- The limit characteristic function `exp(-v s^2/2) cos(a s)` vanishes at `s = π/(2a)`. -/
theorem char_zero (v a : ℝ) (ha : a ≠ 0) :
    Real.exp (-v * (Real.pi / (2 * a)) ^ 2 / 2) * Real.cos (a * (Real.pi / (2 * a))) = 0 := by
  have : a * (Real.pi / (2 * a)) = Real.pi / 2 := by field_simp
  rw [this, Real.cos_pi_div_two, mul_zero]

/-! ### The critical law -/

/-- The mean increments `Δ_r / 2 = 2^{-r-1}` (`r ≥ 1`) sum to `1/2`: partial sums. -/
theorem mean_increments (R : ℕ) :
    ∑ r ∈ Finset.range R, (1 / 2 : ℚ) ^ (r + 2) = 1 / 2 - (1 / 2) ^ (R + 1) := by
  induction R with
  | zero => norm_num
  | succ R ih => rw [Finset.sum_range_succ, ih]; ring

/-- The base law `(5/8, 1/4, 1/8)` has mean `1/2` and variance `1/2`. -/
theorem base_law : (5 / 8 : ℚ) + 1 / 4 + 1 / 8 = 1 ∧ (1 / 4 : ℚ) * 1 + 1 / 8 * 2 = 1 / 2 ∧
    (1 / 4 : ℚ) * 1 + 1 / 8 * 4 - (1 / 2) ^ 2 = 1 / 2 := by norm_num

/-- The stage update `a = (Δ/2 - p (L^- + L^+)) / H` makes the mean increase by exactly `Δ/2`. -/
theorem mean_update (Δ p L₁ L₂ H : ℚ) (hH : H ≠ 0) :
    p * (L₁ + L₂) + ((Δ / 2 - p * (L₁ + L₂)) / H) * H = Δ / 2 := by
  field_simp
  ring

/-- First stage of the critical construction at `n_1 = 2^17`: with `N = 131071` and
`D = 4 sqrt N`, the atoms are `L^- = ⌊N/2 - D⌋ = 64087` and `L^+ = ⌊N/2 + D⌋ = 66983`. -/
theorem critical_stage_one :
    ⌊(131071 : ℝ) / 2 - 4 * Real.sqrt 131071⌋ = 64087 ∧
    ⌊(131071 : ℝ) / 2 + 4 * Real.sqrt 131071⌋ = 66983 := by
  have h1 : (362.03 : ℝ) < Real.sqrt 131071 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt 131071 < 362.04 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  constructor
  · rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith
  · rw [Int.floor_eq_iff]; constructor <;> push_cast <;> linarith

end DegreeCounts

#print axioms DegreeCounts.nn_ge
#print axioms DegreeCounts.stage_one
#print axioms DegreeCounts.stage_two
#print axioms DegreeCounts.dd_lower
#print axioms DegreeCounts.dd_pos_lt
#print axioms DegreeCounts.dd_le
#print axioms DegreeCounts.mass_upper
#print axioms DegreeCounts.mass_lt
#print axioms DegreeCounts.one_current_atom
#print axioms DegreeCounts.no_later_atom
#print axioms DegreeCounts.centering
#print axioms DegreeCounts.bernstein_exponent
#print axioms DegreeCounts.char_zero
#print axioms DegreeCounts.mean_increments
#print axioms DegreeCounts.base_law
#print axioms DegreeCounts.mean_update
#print axioms DegreeCounts.critical_stage_one
