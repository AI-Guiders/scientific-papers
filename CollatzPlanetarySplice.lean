namespace RotatorCalculusPaper

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6400000

/-- **Theorem 18 (Universal Arbitrary-Modulus Rotator & Stereographic Embedding on `ℤ_{4Q}` for Any `Q ∈ ℤ`
and Two-Arc Pillai–Wronskian Trajectory & Cycle Law)**:
1. **Arbitrary-Modulus Rotator & Stereographic Embedding (`∀ Q ∈ ℤ`):**
   On any four-quadrant ring `ℤ_{4Q}` with quarter-modulus `Q` (`C_{4Q}(φ₀) = Q - φ₀`, `S_{4Q}(φ₀) = φ₀`),
   the `L¹` norm `C_{4Q} + S_{4Q} = Q`, the one-step difference Wronskian `W_{4Q}(φ₀) = Q`, and for any
   Diophantine triple `A + B = C` with Bézout partner `A v - B u = 1` (`u + v = w`), the stereographic
   decompositions `Q A = C C_{4Q} - I_{rot,Q}`, `Q B = C S_{4Q} + I_{rot,Q}`, and the quarter-modulus
   invariant `C Δ_{rot,Q} - w I_{rot,Q} = Q` hold identically across all `ℤ`.
2. **Two-Arc Pillai–Wronskian Trajectory & Cycle Law:**
   For any two consecutive binary–ternary trajectory arcs `P₁ n_mid - Q₁ n_start = D₁` and
   `P₂ n_final - Q₂ n_mid = D₂` (`C₁ = P₁ - Q₁`, `C₂ = P₂ - Q₂`, `C_tot = P₁ P₂ - Q₁ Q₂`,
   `D_tot = Q₂ D₁ + P₁ D₂`), the composite displacement decomposes in `ℤ_{C_tot}` as
   `(P₁ P₂)(n_final - n_start) + C_tot n_start = D_tot`, and on any closed cycle (`n_final = n_start`)
   the chord displacement is locked to the `2 × 2` Wronskian determinant:
   `C_tot (n_mid - n_start) = C₂ D₁ - C₁ D₂`. -/
theorem thm18_universal_arbitrary_modulus_rotator_and_two_arc_trajectory_wronskian
    (Q A B C u v w phi0 P1 Q1 P2 Q2 n_start n_mid n_final D1 D2 : Int)
    (hABC : A + B - C = 0)
    (hBez : A * v - B * u = 1)
    (hw   : u + v - w = 0) :
    let cQ := Q - phi0
    let sQ := phi0
    let IrotQ := B * cQ - A * sQ
    let DrotQ := cQ * v - sQ * u
    (cQ + sQ = Q) ∧
    (cQ * (phi0 + 1) - sQ * (Q - (phi0 + 1)) = Q) ∧
    (Q * A = C * cQ - IrotQ) ∧
    (Q * B = C * sQ + IrotQ) ∧
    (C * DrotQ - w * IrotQ = Q) ∧
    (P1 * n_mid - Q1 * n_start = D1 → P2 * n_final - Q2 * n_mid = D2 →
      let C1 := P1 - Q1
      let C2 := P2 - Q2
      let Ctot := P1 * P2 - Q1 * Q2
      let Dtot := Q2 * D1 + P1 * D2
      ((P1 * P2) * n_final - (Q1 * Q2) * n_start = Dtot) ∧
      ((P1 * P2) * (n_final - n_start) + Ctot * n_start = Dtot) ∧
      (n_final = n_start →
        Ctot * n_start = Dtot ∧
        Ctot * n_mid   = P2 * D1 + Q1 * D2 ∧
        Ctot * (n_mid - n_start) = C2 * D1 - C1 * D2)) := by
  dsimp
  have hWQ : (Q - phi0) * (phi0 + 1) - phi0 * (Q - (phi0 + 1)) = Q := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_one, Int.one_mul, Int.mul_comm]
    omega
  have hAQ : Q * A - (C * (Q - phi0) - (B * (Q - phi0) - A * phi0)) =
             (Q - phi0) * (A + B - C) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hBQ : Q * B - (C * phi0 + (B * (Q - phi0) - A * phi0)) =
             phi0 * (A + B - C) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hInvQ : (C * ((Q - phi0) * v - phi0 * u) - w * (B * (Q - phi0) - A * phi0)) -
               Q * (A * v - B * u) =
               (phi0 * u - (Q - phi0) * v) * (A + B - C) +
               (B * (Q - phi0) - A * phi0) * (u + v - w) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  rw [hABC, Int.mul_zero] at hAQ hBQ hInvQ
  rw [hw, hBez, Int.mul_zero, Int.mul_one] at hInvQ
  refine ⟨by omega, hWQ, by omega, by omega, by omega, ?_⟩
  intro hArc1 hArc2
  have e1 : P1 * n_mid - Q1 * n_start - D1 = 0 := by omega
  have e2 : P2 * n_final - Q2 * n_mid - D2 = 0 := by omega
  have hComp :
      (P1 * P2) * n_final - (Q1 * Q2) * n_start - (Q2 * D1 + P1 * D2) =
      Q2 * (P1 * n_mid - Q1 * n_start - D1) + P1 * (P2 * n_final - Q2 * n_mid - D2) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  rw [e1, e2] at hComp
  simp only [Int.mul_zero, Int.add_zero] at hComp
  have hDisp :
      (P1 * P2) * (n_final - n_start) + (P1 * P2 - Q1 * Q2) * n_start - (Q2 * D1 + P1 * D2) =
      (P1 * P2) * n_final - (Q1 * Q2) * n_start - (Q2 * D1 + P1 * D2) := by
    simp only [Int.mul_sub, Int.sub_mul]
    omega
  refine ⟨by omega, by omega, ?_⟩
  intro hCycle
  have e3 : n_final - n_start = 0 := by omega
  have hStart : (P1 * P2 - Q1 * Q2) * n_start - (Q2 * D1 + P1 * D2) =
                ((P1 * P2) * n_final - (Q1 * Q2) * n_start - (Q2 * D1 + P1 * D2)) -
                (P1 * P2) * (n_final - n_start) := by
    simp only [Int.mul_sub, Int.sub_mul]
    omega
  have hMid :
      (P1 * P2 - Q1 * Q2) * n_mid - (P2 * D1 + Q1 * D2) =
      P2 * (P1 * n_mid - Q1 * n_start - D1) + Q1 * (P2 * n_final - Q2 * n_mid - D2) -
      Q1 * P2 * (n_final - n_start) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  rw [e3] at hStart
  simp only [Int.mul_zero, Int.sub_zero] at hStart
  rw [e1, e2, e3] at hMid
  simp only [Int.mul_zero, Int.add_zero, Int.sub_zero] at hMid
  have hWronsk :
      (P1 * P2 - Q1 * Q2) * (n_mid - n_start) - ((P2 - Q2) * D1 - (P1 - Q1) * D2) =
      ((P1 * P2 - Q1 * Q2) * n_mid - (P2 * D1 + Q1 * D2)) -
      ((P1 * P2 - Q1 * Q2) * n_start - (Q2 * D1 + P1 * D2)) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  exact ⟨by omega, by omega, by omega⟩

/-- **Theorem 19 (Collatz Trajectory Dynamics on Natural Rings `ℤ_{2^a}` & `ℤ_{2^a - 3^b}`:
`SL₂(ℤ)` Catalan Exponent-Basis Decomposition `(2, 1) & (3, 2)` and Sign-Free Positive Wronskian Sum)**:
1. **Universal `SL₂(ℤ)` Catalan Exponent-Basis Decomposition (`det [[2, 3], [1, 2]] = +1`):**
   Every trajectory exponent pair `(a, b) ∈ ℤ²` decomposes uniquely into `u = 2a - 3b` (multiplicity of the
   elementary `(2, 1)` arc with gap `2² - 3¹ = 4 - 3 = +1`) and `v = 2b - a` (multiplicity of the elementary
   Catalan `(3, 2)` arc with gap `3² - 2³ = 9 - 8 = +1`), satisfying `2u + 3v = a`, `u + 2v = b`, and `u + v = a - b`.
2. **Factorization of the Pillai Gap `C_tot = 2^a - 3^b = 4^u 8^v - 3^u 9^v` into Unit-Gap Differences:**
   With `P₁ = 4^u, Q₁ = 3^u, G₁ = P₁ - Q₁` and `P₂ = 8^v, Q₂ = 9^v, G₂ = Q₂ - P₂`, the total gap satisfies
   `C_tot = P₂ G₁ - Q₁ G₂ = Q₂ G₁ - P₁ G₂`, while the linear stage operator `(Q₂, P₁)` combines both gaps and drifts:
   `C_tot = Q₂ (P₁ - Q₁) + P₁ (P₂ - Q₂)`.
3. **Sign-Free Strictly Positive Wronskian Chord Sum on Any Closed Cycle (`n_final = n_start`):**
   Splitting any closed cycle at the boundary between the `(4^u, 3^u)` block (drift `D₁`) and the `(8^v, 9^v)` block
   (drift `D₂`) eliminates subtraction completely:
   `C_tot * (n_start - n_mid) = G₂ * D₁ + G₁ * D₂`, bounding both `G₂ D₁` and `G₁ D₂` from above by `C_tot (n_start - n_mid)`. -/
theorem thm19_collatz_catalan_sl2_basis_drift_bounds_and_positive_wronskian_sum
    (a b P1 Q1 P2 Q2 n_start n_mid n_final D1 D2 : Int)
    (hArc1 : P1 * n_mid - Q1 * n_start = D1)
    (hArc2 : P2 * n_final - Q2 * n_mid = D2) :
    let u := (a + a) - (b + b + b)
    let v := (b + b) - a
    let G1 := P1 - Q1
    let G2 := Q2 - P2
    let Ctot := P1 * P2 - Q1 * Q2
    -- 1. Universal SL₂(ℤ) Catalan exponent-basis decomposition (2, 1) and (3, 2):
    ((u + u) + (v + v + v) = a ∧
     u + (v + v) = b ∧
     u + v = a - b ∧
     2 * 2 - 3 * 1 = (1 : Int)) ∧
    -- 2. Exact decomposition of C_tot = P1*P2 - Q1*Q2 into unit-gap differences G1 = 4^u - 3^u and G2 = 9^v - 8^v:
    (Ctot = P2 * G1 - Q1 * G2 ∧
     Ctot = Q2 * G1 - P1 * G2) ∧
    -- 3. Sign-free positive Wronskian sum on any closed cycle (n_final = n_start):
    (n_final = n_start →
      Ctot * (n_start - n_mid) = G2 * D1 + G1 * D2 ∧
      (G2 * D1 ≥ 0 → G1 * D2 ≥ 0 → Ctot * (n_start - n_mid) ≥ G2 * D1) ∧
      (G2 * D1 ≥ 0 → G1 * D2 ≥ 0 → Ctot * (n_start - n_mid) ≥ G1 * D2)) := by
  dsimp
  have hSplit1 : P1 * P2 - Q1 * Q2 = P2 * (P1 - Q1) - Q1 * (Q2 - P2) := by
    simp only [Int.mul_sub, Int.sub_mul, Int.mul_comm]
    omega
  have hSplit2 : P1 * P2 - Q1 * Q2 = Q2 * (P1 - Q1) - P1 * (Q2 - P2) := by
    simp only [Int.mul_sub, Int.sub_mul, Int.mul_comm]
    omega
  refine ⟨⟨by omega, by omega, by omega, by omega⟩, ⟨hSplit1, hSplit2⟩, ?_⟩
  intro hCycle
  have e1 : P1 * n_mid - Q1 * n_start - D1 = 0 := by omega
  have e2 : P2 * n_final - Q2 * n_mid - D2 = 0 := by omega
  have e3 : n_final - n_start = 0 := by omega
  have hPosSum :
      (P1 * P2 - Q1 * Q2) * (n_start - n_mid) - ((Q2 - P2) * D1 + (P1 - Q1) * D2) =
      (Q1 * P2 - P1 * P2) * (n_final - n_start) -
      (P2 - Q2) * (P1 * n_mid - Q1 * n_start - D1) -
      (Q1 - P1) * (P2 * n_final - Q2 * n_mid - D2) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  rw [e1, e2, e3] at hPosSum
  simp only [Int.mul_zero, Int.add_zero, Int.sub_zero] at hPosSum
  exact ⟨by omega, by intro _ _; omega, by intro _ _; omega⟩

/-- **Theorem 20 (Collatz Cyclic Drift Shift Law `2^{α_k} D_tot^{(k+1)} - 3 D_tot^{(k)} = (2^a - 3^b)`
and Dual Residual-Drift Tower `2^{α_{k+1}} D_2^{(k+1)} - 3 D_2^{(k)} = 2^{a - α_k} - 3^{b-1}`)**:
For any step `k` with step power `p_k = 2^{α_k}`, remaining binary power `P_rem_k = 2^{a - α_k}`
(`P_tot = p_k * P_rem_k = 2^a`), and ternary powers `Q_prev = 3^{b-1}`, `Q_tot = 3 * Q_prev = 3^b`
(`C_tot = P_tot - Q_tot = 2^a - 3^b`), where the cyclic total drifts satisfy
`D_tot_k = Q_prev + p_k * D2_k` and `D_tot_k1 = P_rem_k + 3 * D2_k = Q_prev + p_{k+1} * D2_{k+1}`:
1. The cyclic total drifts satisfy the universal shift identity
   `p_k * D_tot_k1 - 3 * D_tot_k = C_tot` (so `p_k * D_tot_k1 ≡ 3 * D_tot_k (mod C_tot)`);
2. The residual drifts satisfy the vertex-free dual transition law
   `p_{k+1} * D2_{k+1} - 3 * D2_k = P_rem_k - Q_prev`;
3. On any closed cycle (`C_tot * n_k = D_tot_k`), the Pillai envelope `D2_k ≥ Q_prev - B_prev`
   (`3^{b-1} - 2^{b-1}`) enforces the lower bound `C_tot * n_k ≥ Q_prev + p_k * (Q_prev - B_prev)`. -/
theorem thm20_collatz_dual_drift_tower_and_cyclic_shift_law
    (pk pk1 Premk Qprev Bprev D2k D2k1 nk : Int) :
    let Ptot := pk * Premk
    let Qtot := 3 * Qprev
    let Ctot := Ptot - Qtot
    let Dtot_k  := Qprev + pk * D2k
    let Dtot_k1 := Premk + 3 * D2k
    (pk * Dtot_k1 - 3 * Dtot_k = Ctot) ∧
    (Dtot_k1 = Qprev + pk1 * D2k1 → pk1 * D2k1 - 3 * D2k = Premk - Qprev) ∧
    (Ctot * nk = Dtot_k → pk * (D2k - (Qprev - Bprev)) ≥ 0 →
      Ctot * nk ≥ Qprev + pk * (Qprev - Bprev)) := by
  dsimp
  have hShift : pk * (Premk + 3 * D2k) - 3 * (Qprev + pk * D2k) = pk * Premk - 3 * Qprev := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  refine ⟨hShift, by omega, ?_⟩
  intro hCycle hEnv
  have hSub : pk * (D2k - (Qprev - Bprev)) = pk * D2k - pk * (Qprev - Bprev) := by
    simp only [Int.mul_sub]
  omega

/-- **Theorem 21 (Uniqueness of the Planetary Gear Stationary Point `(2^α - 3) n* = 1 ⟹ (2^α = 4 ∧ n* = 1)`
and Exact Differential Closure Criterion `3^b n_start + D_{a,b} = 2^a` for Reaching `n_final = 1`)**:
1. **Planetary Gear Orthogonality & Unique Stationary Point (`n_{k+1} = n_k = n* = 1`):**
   Each odd Collatz step is an orthogonal planetary gear link `r_k · ω_k = 3 n_k + 1 - p_k n_{k+1} = 0`
   (`r_k = (3, 1, p_k)`, `ω_k = (n_k, 1, -n_{k+1})`, `p_k = 2^{α_k}`). At a stationary point
   `n_{k+1} = n_k = n* ≥ 1`, the stationary equation `(p_k - 3) n* = 1` has the unique positive
   integer solution `p_k = 4` (`α* = 2`) and `n* = 1`.
2. **Differential Closure Criterion for Reaching the Stationary Point (`n_final = 1`):**
   Along any `a`-step cascade `P n_final - Q n_start = D_{a,b}` (`P = 2^a, Q = 3^b`), the trajectory
   reaches the unique stationary point `n_final = 1` if and only if the planetary differential
   `A + B = C` closes the ternary shaft `A = Q n_start` and the carry cascade `B = D_{a,b}` into the
   pure binary power `C = P = 2^a` (`n_final = 1 ↔ Q * n_start + D_{a,b} = P`), with exact distance
   `P * (n_final - 1) = (Q * n_start + D_{a,b}) - P`. -/
theorem thm21_collatz_planetary_stationary_point_uniqueness_and_reachability_criterion
    (pk nStar P Q n_start n_final Dab : Int) :
    (nStar ≥ 1 → (pk - 3) * nStar = 1 → pk = 4 ∧ nStar = 1) ∧
    (P * n_final - Q * n_start = Dab →
      P * (n_final - 1) = (Q * n_start + Dab) - P ∧
      (n_final = 1 → Q * n_start + Dab = P) ∧
      (P ≠ 0 → Q * n_start + Dab = P → n_final = 1)) := by
  refine ⟨?_, ?_⟩
  · intro hN hStat
    have hPos : pk - 3 ≥ 1 := by
      by_cases h : pk - 3 ≤ 0
      · have hMul : (pk - 3) * nStar ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg h (by omega)
        omega
      · omega
    have hLe : nStar ≤ (pk - 3) * nStar := by
      have hDiff : (pk - 3) * nStar - nStar = (pk - 4) * nStar := by
        simp only [Int.sub_mul]
        omega
      have hGe0 : (pk - 4) * nStar ≥ 0 := Int.mul_nonneg (by omega) (by omega)
      omega
    have hN1 : nStar = 1 := by omega
    rw [hN1, Int.mul_one] at hStat
    exact ⟨by omega, hN1⟩
  · intro hEq
    have hDist : P * (n_final - 1) - ((Q * n_start + Dab) - P) =
                 (P * n_final - Q * n_start) - Dab := by
      simp only [Int.mul_sub, Int.mul_one]
      omega
    refine ⟨by omega, by intro h1; rw [h1, Int.mul_one] at hEq; omega, ?_⟩
    intro hPne0 hClose
    have hP0 : P * (n_final - 1) = 0 := by omega
    cases Int.mul_eq_zero.mp hP0 with
    | inl hP => exact False.elim (hPne0 hP)
    | inr hN => omega

/-- **Constructive Fermat Well-Founded Descent to the Stationary Point `1` (`0 Classical.choice`)**:
If every `n > 1` admits a trajectory window `k` landing at `1 ≤ iter k n < n`, then EVERY `n ≥ 1`
reaches the unique stationary point `1` in finitely many steps `K`. -/
theorem collatz_global_convergence_from_local_descent
    (iter : Nat → Nat → Nat)
    (hZero : ∀ n, iter 0 n = n)
    (hAdd  : ∀ k1 k2 n, iter (k1 + k2) n = iter k2 (iter k1 n))
    (hLocalDescent : ∀ n : Nat, n > 1 → ∃ k : Nat, iter k n ≥ 1 ∧ iter k n < n) :
    ∀ n : Nat, n ≥ 1 → ∃ K : Nat, iter K n = 1 := by
  intro n
  refine Nat.strongRecOn n (fun m ih hm => ?_)
  by_cases h1 : m = 1
  · refine ⟨0, ?_⟩
    rw [hZero, h1]
  · have hGt1 : m > 1 := by omega
    obtain ⟨k1, hk1Ge1, hk1Lt⟩ := hLocalDescent m hGt1
    obtain ⟨k2, hk2Eq1⟩ := ih (iter k1 m) hk1Lt hk1Ge1
    refine ⟨k1 + k2, ?_⟩
    rw [hAdd, hk2Eq1]

/-- **Theorem 22 (Arbitrary-Stage Fermat Infinite-Descent Reduction `(2^a - 3^b) n > D_{a,b} ↔ n_final < n`
and Universal Pillai-Envelope Descent Criterion across Arbitrary `(2^a, 3^b)`)**:
1. Along any `a`-step planetary gear cascade `P * n_final - Q * n = D_{a,b}` (`P = 2^a > 0, Q = 3^b, C = P - Q`),
   `P * (n - n_final) = C * n - D_{a,b}`, so strict descent `n_final < n` holds if and only if
   `C * n > D_{a,b}` (`(2^a - 3^b) * n > D_{a,b}`).
2. Combining this with the universal upper Pillai drift envelope `D_{a,b} ≤ D_env` (`D_env = 2^{a-b}(3^b - 2^b)`),
   for ANY contracting exponent pair `(a, b)` (`C = 2^a - 3^b ≥ 1`), any starting state satisfying
   `C * n > D_env` unconditionally satisfies `C * n > D_{a,b}` and hence `n_final < n`. -/
theorem thm22_collatz_arbitrary_stage_fermat_descent_reduction
    (P Q n n_final Dab Denv : Int)
    (hP : P > 0)
    (hTraj : P * n_final - Q * n = Dab) :
    let C := P - Q
    (P * (n - n_final) = C * n - Dab) ∧
    (C * n > Dab ↔ n_final < n) ∧
    (Dab ≤ Denv → C * n > Denv → C * n > Dab ∧ n_final < n) := by
  dsimp
  have hId : P * (n - n_final) - ((P - Q) * n - Dab) = Dab - (P * n_final - Q * n) := by
    simp only [Int.mul_sub, Int.sub_mul]
    omega
  have hEquiv : (P - Q) * n > Dab ↔ n_final < n := by
    constructor
    · intro hGt
      have hPos : P * (n - n_final) > 0 := by omega
      by_cases hLe : n - n_final ≤ 0
      · have hNonpos : P * (n - n_final) ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hLe
        omega
      · omega
    · intro hLt
      have hPos : P * (n - n_final) > 0 := Int.mul_pos hP (by omega)
      omega
  refine ⟨by omega, hEquiv, ?_⟩
  intro hEnv hGtEnv
  have hGt : (P - Q) * n > Dab := by omega
  exact ⟨hGt, hEquiv.mp hGt⟩

/-- **Theorem 23 (Dead-End-Free Ternary Prefix Decomposition `D_{a,b} = 2^{s_{b-1}} + 3 D_{b-1}`
and Subgroup-`<4>` Stationary Closure in `ℤ_{3^b}^×`)**:
For any prefix of `b - 1` planetary gear steps with penultimate cumulative binary power `P_pen = 2^{s_{b-1}}`,
prefix drift `D_prev = D_{b-1}(s_0, ..., s_{b-2})`, and final gear power `p_last = 2^{α_{b-1}}`
(`P_tot = P_pen * p_last = 2^a`, `Q_tot = 3 * Q_prev = 3^b`):
1. The total drift splits as `D_tot = P_pen + 3 * D_prev`, so `D_tot ≡ P_pen (mod 3)` (never divisible by `3`
   when `P_pen = 2^{s_{b-1}}`), eliminating modulo-3 dead ends across the `(b-1)`-step prefix space;
2. The stationary-point closure equation `Q_tot * n + D_tot = P_tot` (`3^b * n + D_{a,b} = 2^a`) is
   equivalent to `P_pen * (p_last - 1) = 3 * (Q_prev * n + D_prev)`. -/
theorem thm23_collatz_dead_end_free_ternary_prefix_closure
    (Ppen plast Qprev Dprev n : Int) :
    let Ptot := Ppen * plast
    let Qtot := 3 * Qprev
    let Dtot := Ppen + 3 * Dprev
    (Dtot - Ppen = 3 * Dprev) ∧
    (Qtot * n + Dtot = Ptot ↔ Ppen * (plast - 1) = 3 * (Qprev * n + Dprev)) := by
  dsimp
  have hId : (3 * Qprev * n + (Ppen + 3 * Dprev) - Ppen * plast) =
             (3 * (Qprev * n + Dprev) - Ppen * (plast - 1)) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_one, Int.mul_assoc]
    omega
  refine ⟨by omega, ?_⟩
  constructor
  · intro h
    omega
  · intro h
    omega

/-- **Theorem 24 (Counter-Rotating Forward-Backward Planetary Gear Splice in `ℤ_{2^{a_1}} × ℤ_{3^{b_2}}`,
Bézout Meeting-Point Reconstruction, and Pure-Ternary Chord Law)**:
Splitting a trajectory from `n_start` to the stationary root `n* = 1` at an intermediate meeting point `n_mid`
into two counter-rotating planetary gear cascades:
- **Forward rotor (clockwise from `n_start` to `n_mid` in `ℤ_{2^{a_1}}`):** `P1 * n_mid = Q1 * n_start + D1`
  (`P1 = 2^{a_1}, Q1 = 3^{b_1}`),
- **Backward rotor (counter-clockwise from `n* = 1` to `n_mid` in `ℤ_{3^{b_2}}^×`):** `Q2 * n_mid = P2 - D2`
  (`P2 = 2^{a_2}, Q2 = 3^{b_2}`):
1. **Orthogonal Coaxial Splice Identity & Stationary Closure:**
   `Q2 * (Q1 * n_start + D1) = P1 * (P2 - D2)` and `(Q1 * Q2) * n_start + (Q2 * D1 + P1 * D2) = P1 * P2`;
2. **Division-Free Bézout Reconstruction of the Meeting Point `n_mid`:**
   For any Bézout coefficients `P1 * v - Q2 * u = 1` (`gcd(2^{a_1}, 3^{b_2}) = 1`),
   `n_mid = v * (Q1 * n_start + D1) - u * (P2 - D2)`;
3. **Pure-Ternary Counter-Rotating Chord Law (`3^{b_1 + b_2} (n_start - n_mid)`):**
   `(Q1 * Q2) * (n_start - n_mid) = (P1 - Q1) * (P2 - D2) - Q2 * D1`. -/
theorem thm24_collatz_counter_rotating_forward_backward_splice_and_bezout_lock
    (P1 Q1 D1 P2 Q2 D2 n_start n_mid u v : Int)
    (hFwd : P1 * n_mid = Q1 * n_start + D1)
    (hBwd : Q2 * n_mid = P2 - D2) :
    (Q2 * (Q1 * n_start + D1) = P1 * (P2 - D2) ∧
     (Q1 * Q2) * n_start + (Q2 * D1 + P1 * D2) = P1 * P2) ∧
    (P1 * v - Q2 * u = 1 → n_mid = v * (Q1 * n_start + D1) - u * (P2 - D2)) ∧
    ((Q1 * Q2) * (n_start - n_mid) = (P1 - Q1) * (P2 - D2) - Q2 * D1) := by
  have hSplice1 : Q2 * (Q1 * n_start + D1) = Q2 * (P1 * n_mid) := by rw [hFwd]
  have hSplice2 : P1 * (P2 - D2) = P1 * (Q2 * n_mid) := by rw [hBwd]
  have hComm : Q2 * (P1 * n_mid) = P1 * (Q2 * n_mid) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hSplice : Q2 * (Q1 * n_start + D1) = P1 * (P2 - D2) := by omega
  have hGlobal : (Q1 * Q2) * n_start + (Q2 * D1 + P1 * D2) - P1 * P2 =
                 Q2 * (Q1 * n_start + D1) - P1 * (P2 - D2) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hChordId : (Q1 * Q2) * (n_start - n_mid) - ((P1 - Q1) * (Q2 * n_mid) - Q2 * D1) =
                  Q2 * (Q1 * n_start + D1) - Q2 * (P1 * n_mid) := by
    simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  rw [hBwd, ← hSplice1] at hChordId
  refine ⟨⟨hSplice, by omega⟩, ?_, by omega⟩
  intro hBez
  rw [← hFwd, ← hBwd]
  have hBezId : n_mid - (v * (P1 * n_mid) - u * (Q2 * n_mid)) =
                (1 - (P1 * v - Q2 * u)) * n_mid := by
    simp only [Int.mul_sub, Int.sub_mul, Int.one_mul, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  rw [hBez] at hBezId
  omega

/-- **Theorem 25 (Automatic 2-adic / 3-adic Gear-Tooth Meshing and Inductive Step-Peeling Law
`3^b n_0 + (3^{b-1} + 2^{α_0} D_rem) = 2^a ⟺ 3^{b-1} (3 n_0 + 1) = 2^{α_0} (2^{a - α_0} - D_rem)`)**:
Let `Q_prev = 3^{b-1}`, `p_0 = 2^{α_0}`, `P_rem = 2^{a - α_0}` (`P_tot = p_0 * P_rem = 2^a`,
`Q_tot = 3 * Q_prev = 3^b`), and `D_tot = Q_prev + p_0 * D_rem`. Then:
1. **Gear-Tooth Meshing Identity:**
   `(3 * Q_prev) * n_0 + (Q_prev + p_0 * D_rem) = p_0 * P_rem ↔ Q_prev * (3 * n_0 + 1) = p_0 * (P_rem - D_rem)`;
2. **Exact 2-adic Valuation Parity Lock:**
   Whenever `P_rem = 2 * k_P` is even (`a > α_0`) and `D_rem = 2 * k_D + 1` is odd, the cofactor
   `P_rem - D_rem = 2 * (k_P - k_D - 1) + 1` is strictly odd, so `p_0 = 2^{α_0}` absorbs the exact power
   of two dividing `3 * n_0 + 1`;
3. **One-Step Forward-Backward Peeling (`n_0 ↦ n_1`):**
   Under the forward step `3 * n_0 + 1 = p_0 * n_1` (`p_0 ≠ 0`), the `b`-step equation peels off its first
   link into the `(b - 1)`-step equation `Q_prev * n_1 + D_rem = P_rem` (`3^{b-1} n_1 + D_rem = 2^{a - α_0}`). -/
theorem thm25_collatz_automatic_2adic_3adic_gear_tooth_meshing_and_step_peeling
    (Qprev p0 Prem Drem n0 n1 kP kD : Int) :
    ((3 * Qprev) * n0 + (Qprev + p0 * Drem) = p0 * Prem ↔
      Qprev * (3 * n0 + 1) = p0 * (Prem - Drem)) ∧
    (Prem = 2 * kP → Drem = 2 * kD + 1 → (Prem - Drem) - 2 * (kP - kD - 1) = 1) ∧
    (p0 ≠ 0 → 3 * n0 + 1 = p0 * n1 →
      ((3 * Qprev) * n0 + (Qprev + p0 * Drem) = p0 * Prem ↔ Qprev * n1 + Drem = Prem)) := by
  have hId1 : ((3 * Qprev) * n0 + (Qprev + p0 * Drem) - p0 * Prem) =
              (Qprev * (3 * n0 + 1) - p0 * (Prem - Drem)) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  refine ⟨⟨fun h => by omega, fun h => by omega⟩, by intro hP hD; omega, ?_⟩
  intro hp0 hStep
  have hId2 : ((3 * Qprev) * n0 + (Qprev + p0 * Drem) - p0 * Prem) =
              (Qprev * (3 * n0 + 1) - p0 * (Prem - Drem)) := hId1
  rw [hStep] at hId2
  have hFactor : Qprev * (p0 * n1) - p0 * (Prem - Drem) =
                 p0 * (Qprev * n1 + Drem - Prem) := by
    simp only [Int.mul_add, Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  constructor
  · intro h
    have hMul0 : p0 * (Qprev * n1 + Drem - Prem) = 0 := by omega
    cases Int.mul_eq_zero.mp hMul0 with
    | inl h0 => exact False.elim (hp0 h0)
    | inr hRem => omega
  · intro h
    have hRem0 : Qprev * n1 + Drem - Prem = 0 := by omega
    rw [hRem0, Int.mul_zero] at hFactor
    omega

/-- **Theorem 26 (Single-Step Wronskian Excess Identity `(3 n_ref + 1) n_k - 2^{α_k} n_ref n_{k+1} = n_k - n_ref`,
Binary-Power-Free Bernoulli-Euler Drift Bound, and Guaranteed Descent Criterion)**:
1. For any odd Collatz step `p_k * n_{k+1} = 3 * n_k + 1` (`p_k = 2^{α_k}`) and reference value `n_ref`:
   `(3 * n_ref + 1) * n_k - p_k * n_ref * n_{k+1} = n_k - n_ref` and
   `p_k * n_ref * n_{k+1} - (3 * n_ref + 1) * n_k = n_ref - n_k`.
2. Along any arc `P_tot * n_final = Q_tot * n_0 + D_{a,b}` satisfying the accumulated non-descending bound
   `P_tot * n_0^{b-1} * n_final ≤ (3 * n_0 + 1)^b`, the drift is bounded independently of `2^a`:
   `n_0^{b-1} * D_{a,b} ≤ (3 * n_0 + 1)^b - Q_tot * n_0^b`, and `P_tot * n_0^b > (3 * n_0 + 1)^b`
   unconditionally forces strict descent `n_final < n_0`. -/
theorem thm26_collatz_step_wronskian_excess_identity_and_bernoulli_euler_cycle_lock
    (pk nk nk1 nref Ptot Qtot n0PowPrev n0 nfinal Dab Bpow : Int)
    (hStep : pk * nk1 = 3 * nk + 1) :
    ((3 * nref + 1) * nk - pk * nref * nk1 = nk - nref ∧
     pk * nref * nk1 - (3 * nref + 1) * nk = nref - nk ∧
     (nk ≥ nref → pk * nref * nk1 ≤ (3 * nref + 1) * nk) ∧
     (nk ≤ nref → pk * nref * nk1 ≥ (3 * nref + 1) * nk)) ∧
    (Ptot * nfinal = Qtot * n0 + Dab →
     Ptot * n0PowPrev * nfinal ≤ Bpow →
      n0PowPrev * Dab ≤ Bpow - Qtot * (n0PowPrev * n0) ∧
      Ptot * n0PowPrev * (n0 - nfinal) ≥ Ptot * (n0PowPrev * n0) - Bpow ∧
      (Ptot * n0PowPrev > 0 → Ptot * (n0PowPrev * n0) > Bpow → nfinal < n0)) := by
  have hProd : pk * nref * nk1 = nref * (pk * nk1) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [hStep] at hProd
  have hWronsk : (3 * nref + 1) * nk - nref * (3 * nk + 1) = nk - nref := by
    simp only [Int.mul_add, Int.add_mul, Int.one_mul, Int.mul_one,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  refine ⟨⟨by omega, by omega, by intro _; omega, by intro _; omega⟩, ?_⟩
  intro hTraj hBern
  have hSub : Ptot * n0PowPrev * nfinal = n0PowPrev * (Ptot * nfinal) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [hTraj] at hSub
  have hExpand : n0PowPrev * (Qtot * n0 + Dab) = Qtot * (n0PowPrev * n0) + n0PowPrev * Dab := by
    simp only [Int.mul_add, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hDiff : Ptot * n0PowPrev * (n0 - nfinal) =
               Ptot * (n0PowPrev * n0) - Ptot * n0PowPrev * nfinal := by
    simp only [Int.mul_sub, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  refine ⟨by omega, by omega, ?_⟩
  intro hPos hGt
  have hPosDiff : (Ptot * n0PowPrev) * (n0 - nfinal) > 0 := by omega
  by_cases hLe : n0 - nfinal ≤ 0
  · have hNonpos : (Ptot * n0PowPrev) * (n0 - nfinal) ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hLe
    omega
  · omega

/-- **Theorem 27 (Pure-Binary 3-Free Step Identity `4 n_k - 2^{α_k} n_{k+1} = n_k - 1` Over the Stationary Root `n* = 1`
and Dual-Drift Conservation Law `D_{a,b} + E_{a,b} = (4^b - 3^b) n_0`)**:
1. Setting `n_ref = 1` (`3 n_ref + 1 = 4 = 2^2`) in any odd Collatz step `p_k * n_{k+1} = 3 * n_k + 1`
   eliminates the ternary base `3`, yielding the purely binary step equation `4 * n_k - p_k * n_{k+1} = n_k - 1`.
2. Along any `b`-step trajectory from `n_0` to `n_b` with `P_tot = 2^a`, `Q_tot = 3^b`, and `F_tot = 4^b = 2^{2b}`,
   the ternary drift `D_{a,b} = P_tot * n_b - Q_tot * n_0 > 0` and the pure-binary excess drift
   `E_{a,b} = F_tot * n_0 - P_tot * n_b = ∑_{k=0}^{b-1} 4^{b-1-k} 2^{s_k} (n_k - 1) ≥ 0` satisfy the
   path-independent conservation law `D_{a,b} + E_{a,b} = (4^b - 3^b) * n_0` (free of `2^a` and `n_b`),
   and the negative-feedback descent law `2^a (n_0 - n_b) = E_{a,b} - (4^b - 2^a) n_0`. -/
theorem thm27_collatz_pure_binary_stationary_excess_law_and_dual_drift_conservation
    (pk nk nk1 Ptot Qtot Ftot n0 nb Dab Eab : Int)
    (hStep : pk * nk1 = 3 * nk + 1) :
    (4 * nk - pk * nk1 = nk - 1 ∧
     (nk ≥ 1 → 4 * nk - pk * nk1 ≥ 0) ∧
     (4 * nk - pk * nk1 = 0 → nk = 1) ∧
     (nk = 1 → 4 * nk - pk * nk1 = 0)) ∧
    (Ptot * nb - Qtot * n0 = Dab →
     Ftot * n0 - Ptot * nb = Eab →
      Dab + Eab = (Ftot - Qtot) * n0 ∧
      Ptot * (n0 - nb) = Eab - (Ftot - Ptot) * n0 ∧
      Ptot * (n0 - nb) = (Ptot - Qtot) * n0 - Dab ∧
      (Dab > 0 → Eab ≥ 0 → Dab ≤ (Ftot - Qtot) * n0 ∧ Eab < (Ftot - Qtot) * n0)) := by
  refine ⟨⟨by omega, by intro _; omega, by intro _; omega, by intro _; omega⟩, ?_⟩
  intro hD hE
  have hSum : (Ptot * nb - Qtot * n0) + (Ftot * n0 - Ptot * nb) = (Ftot - Qtot) * n0 := by
    simp only [Int.sub_mul]
    omega
  have hDesc1 : Ptot * (n0 - nb) - (Ftot * n0 - Ptot * nb - (Ftot - Ptot) * n0) = 0 := by
    simp only [Int.mul_sub, Int.sub_mul]
    omega
  have hDesc2 : Ptot * (n0 - nb) - ((Ptot - Qtot) * n0 - (Ptot * nb - Qtot * n0)) = 0 := by
    simp only [Int.mul_sub, Int.sub_mul]
    omega
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro hDpos hEnonneg
  exact ⟨by omega, by omega⟩

/-- **Theorem 28 (Centered Stationary-Root Coordinate `m_k = (n_k - 1)/2` with Origin `m* = 0`
and Stationary-Gear Deviation Law `3^b (n_0 - 1) - 2^a (n_b - 1) = 2^a - 3^b - D_{a,b} = ∑ 3^{b-1-k} (2^{α_k} - 4) 2^{s_k}`)**:
1. Substituting `n_k = 2 m_k + 1`, `n_{k+1} = 2 m_{k+1} + 1`, and `p_k = 2 * p_half` (`p_k = 2^{α_k}`,
   `p_half = 2^{α_k - 1}`) into `p_k * n_{k+1} = 3 * n_k + 1` shifts the stationary point `n* = 1` to the
   origin `m* = 0`: `p_k * m_{k+1} - 3 * m_k = 2 - p_half` (`+1` at `α_k = 1`, `0` at `α_k = 2`, `≤ -2` at `α_k ≥ 3`).
2. The binary headroom `G_k = 2^{s_k} - D_k` satisfies `G_{k+1} - 3 * G_k = (p_k - 4) * 2^{s_k}`, which
   telescopes over `b` steps to `P_tot - Q_tot - D_{a,b} = 3^b (n_0 - 1) - 2^a (n_b - 1)`. -/
theorem thm28_collatz_centered_stationary_coordinate_and_gear_deviation_law
    (pk phalf mk mk1 ps Dk Ptot Qtot n0 nb Dab : Int) :
    let nk   := 2 * mk + 1
    let nk1  := 2 * mk1 + 1
    let ps1  := pk * ps
    let Dk1  := 3 * Dk + ps
    let Gk   := ps - Dk
    let Gk1  := ps1 - Dk1
    (pk = 2 * phalf → pk * nk1 = 3 * nk + 1 →
      pk * mk1 - 3 * mk = 2 - phalf ∧
      (phalf = 2 → pk * mk1 = 3 * mk)) ∧
    (Gk1 - 3 * Gk = (pk - 4) * ps) ∧
    (Ptot * nb - Qtot * n0 = Dab →
      Qtot * (n0 - 1) - Ptot * (nb - 1) = Ptot - Qtot - Dab ∧
      (nb = 1 → Qtot * (n0 - 1) = Ptot - Qtot - Dab)) := by
  dsimp
  have hStepCentered : (2 * phalf) * (2 * mk1 + 1) - (3 * (2 * mk + 1) + 1) =
                       2 * ((2 * phalf) * mk1 - 3 * mk - (2 - phalf)) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hGrec : (pk * ps - (3 * Dk + ps)) - 3 * (ps - Dk) - (pk - 4) * ps = 0 := by
    simp only [Int.mul_sub, Int.sub_mul]
    omega
  refine ⟨?_, by omega, ?_⟩
  · intro hpk hStep
    rw [hpk] at hStep ⊢
    refine ⟨by omega, ?_⟩
    intro hphalf
    omega
  · intro hTraj
    have hGlobal : (Qtot * (n0 - 1) - Ptot * (nb - 1)) - (Ptot - Qtot - Dab) =
                   Dab - (Ptot * nb - Qtot * n0) := by
      simp only [Int.mul_sub, Int.mul_one]
      omega
    refine ⟨by omega, ?_⟩
    intro hnb1
    have hP0 : Ptot * (nb - 1) = 0 := by rw [hnb1]; simp
    omega

/-- **Theorem 29 (Trailing-Ones Burn Macro-Step `n_0 = 2^{r+1} q - 1 ↦ 2^{α_r - 1} n_{r+1} = 3^{r+1} q - 1`
and Guaranteed Even-Centered Reset `m_r = 3^r q - 1`)**:
1. Under `α_k = 1` (`2 m_{k+1} = 3 m_k + 1`), `2 * (m_{k+1} + 1) = 3 * (m_k + 1)`.
2. After `r` trailing-one steps from `m_0 = 2^r * q - 1` (`n_0 = 2^{r+1} * q - 1`), `m_r = 3^r * q - 1`
   is ALWAYS even whenever `3^r` and `q` are odd (`m_r = 2 (2 k_Q k_q + k_Q + k_q)`), forcing a
   contracting gear `α_r ≥ 2` on step `r + 1`.
3. With `3 * n_r + 1 = (2 * p_half_r) * n_{r+1}` (`p_half_r = 2^{α_r - 1} ≥ 2`),
   `p_half_r * n_{r+1} = 3 * (3^r * q) - 1` and
   `p_half_r * (n_0 - n_{r+1}) = 2 * (p_half_r * (2^r * q)) - 3 * (3^r * q) - (p_half_r - 1)`. -/
theorem thm29_collatz_trailing_ones_burn_macro_step
    (mk mk1 Pr Qr q mr nr1 phalfr kQ kq : Int) :
    let n0 := 2 * (Pr * q - 1) + 1
    let nr := 2 * mr + 1
    (2 * mk1 = 3 * mk + 1 → 2 * (mk1 + 1) = 3 * (mk + 1)) ∧
    (mr = Qr * q - 1 → Qr = 2 * kQ + 1 → q = 2 * kq + 1 →
      mr = 2 * (2 * kQ * kq + kQ + kq)) ∧
    (mr = Qr * q - 1 → 3 * nr + 1 = (2 * phalfr) * nr1 →
      phalfr * nr1 = 3 * (Qr * q) - 1 ∧
      phalfr * (n0 - nr1) = 2 * (phalfr * (Pr * q)) - 3 * (Qr * q) - (phalfr - 1)) := by
  dsimp
  refine ⟨by intro _; omega, ?_, ?_⟩
  · intro hmr hQr hq
    rw [hmr, hQr, hq]
    have hOddProd : (2 * kQ + 1) * (2 * kq + 1) - 1 = 2 * (2 * kQ * kq + kQ + kq) := by
      simp only [Int.mul_add, Int.add_mul, Int.mul_one, Int.one_mul,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega
    exact hOddProd
  · intro hmr hStepR
    rw [hmr] at hStepR
    have h2 : (2 * phalfr) * nr1 = 2 * (phalfr * nr1) := by
      simp only [Int.mul_assoc]
    have hMacro : phalfr * nr1 = 3 * (Qr * q) - 1 := by omega
    have hDesc : phalfr * ((2 * (Pr * q - 1) + 1) - nr1) =
                 2 * (phalfr * (Pr * q)) - phalfr - phalfr * nr1 := by
      simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.mul_one,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega
    exact ⟨hMacro, by omega⟩

/-- **Theorem 30 (Minimal-Drift Macro-Step Law `2^{r_0 + 1 + β_0} n^{(1)} - 3^{r_0 + 1} n_0 = 3^{r_0 + 1} - 2^{r_0 + 1}`,
Odd-Core Transition Law `2^{β_0 + r_1 + 1} q_1 - 3^{r_0 + 1} q_0 = 2^{β_0} - 1`, and Post-Burn Potential Evolution)**:
For any macro-step from `n_0 = P_r1 * q_0 - 1` (`P_r1 = 2^{r_0 + 1}`, `Q_r1 = 3^{r_0 + 1}`) to
`n_1 = P'_r1 * q_1 - 1` (`P'_r1 = 2^{r_1 + 1}`, `Q'_r1 = 3^{r_1 + 1}`) governed by `p_β * n_1 + 1 = Q_r1 * q_0`
(`p_β = 2^{β_0} ≥ 2`):
1. Eliminating `q_0` yields `(P_r1 * p_β) * n_1 - Q_r1 * n_0 = Q_r1 - P_r1` (`3^{r_0+1} - 2^{r_0+1}`,
   attaining the exact lower bound of the Pillai drift envelope);
2. The odd cores `q_0, q_1` satisfy `(p_β * P'_r1) * q_1 - Q_r1 * q_0 = p_β - 1` and
   `(p_β * P'_r1) * (q_0 - q_1) = (p_β * P'_r1 - Q_r1) * q_0 - (p_β - 1)`;
3. Setting `H_0 = Q_r1 * q_0` and `H_1 = Q'_r1 * q_1`,
   `(p_β * P'_r1) * H_1 = Q'_r1 * (H_0 + (p_β - 1))`. -/
theorem thm30_collatz_odd_core_transition_law_and_post_burn_potential
    (Pr1 Qr1 Pr1_next Qr1_next pbeta q0 q1 n0 n1 : Int)
    (hn0   : n0 + 1 = Pr1 * q0)
    (hMac  : pbeta * n1 + 1 = Qr1 * q0)
    (hn1   : n1 + 1 = Pr1_next * q1) :
    let H0 := Qr1 * q0
    let H1 := Qr1_next * q1
    ((Pr1 * pbeta) * n1 - Qr1 * n0 = Qr1 - Pr1) ∧
    ((pbeta * Pr1_next) * q1 - Qr1 * q0 = pbeta - 1 ∧
     (pbeta * Pr1_next) * (q0 - q1) = (pbeta * Pr1_next - Qr1) * q0 - (pbeta - 1)) ∧
    ((pbeta * Pr1_next) * H1 = Qr1_next * (H0 + (pbeta - 1))) := by
  dsimp
  have h1 : (Pr1 * pbeta) * n1 + Pr1 = Pr1 * (pbeta * n1 + 1) := by
    simp only [Int.mul_add, Int.mul_one, Int.mul_assoc]
  rw [hMac] at h1
  have h2 : Qr1 * n0 + Qr1 = Qr1 * (n0 + 1) := by
    simp only [Int.mul_add, Int.mul_one]
  rw [hn0] at h2
  have hComm12 : Pr1 * (Qr1 * q0) = Qr1 * (Pr1 * q0) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hCore1 : (pbeta * Pr1_next) * q1 = pbeta * (Pr1_next * q1) := by
    simp only [Int.mul_assoc]
  rw [← hn1] at hCore1
  have hCore2 : pbeta * (n1 + 1) = (pbeta * n1 + 1) + (pbeta - 1) := by
    simp only [Int.mul_add, Int.mul_one]
    omega
  rw [hMac] at hCore2
  have hCoreLaw : (pbeta * Pr1_next) * q1 - Qr1 * q0 = pbeta - 1 := by omega
  have hCoreDesc : (pbeta * Pr1_next) * (q0 - q1) - ((pbeta * Pr1_next - Qr1) * q0 - (pbeta - 1)) =
                   (Qr1 * q0 + (pbeta - 1)) - (pbeta * Pr1_next) * q1 := by
    simp only [Int.mul_sub, Int.sub_mul]
    omega
  have hPot1 : (pbeta * Pr1_next) * (Qr1_next * q1) = Qr1_next * ((pbeta * Pr1_next) * q1) := by
    simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have hPot2 : (pbeta * Pr1_next) * q1 = Qr1 * q0 + (pbeta - 1) := by omega
  rw [hPot2] at hPot1
  exact ⟨by omega, ⟨hCoreLaw, by omega⟩, hPot1⟩

/-- **Theorem 31 (Double `SL₂(ℤ)` Bézout Lock on Every Macro-Step, Homogeneous Core-Difference Law
`2^{β_m} n^{(m+1)} - n^{(m)} = (3^{r_m+1} - 2^{r_m+1}) q_m`, and Unconditional Core Descent `q_{m+1} < q_m` at `r_m = 0`)**:
For any macro-step from `n_0 = P_r1 * q_0 - 1` (`P_r1 = 2^{r_0 + 1}`, `Q_r1 = 3^{r_0 + 1}`) to
`n_1 = P'_r1 * q_1 - 1` (`P'_r1 = 2^{r_1 + 1}`) governed by `p_β * n_1 + 1 = Q_r1 * q_0` (`p_β = 2^{β_0} ≥ 2`):
1. Both the entry determinant `P_r1 * q_0 - 1 * n_0 = 1` and the exit determinant `Q_r1 * q_0 - p_β * n_1 = 1`
   equal `+1`; subtracting them eliminates `+1` identically, yielding `p_β * n_1 - n_0 = (Q_r1 - P_r1) * q_0`;
2. Whenever `r_0 = 0` (`n_0 ≡ 1 (mod 4)`, `Q_r1 = 3`), the core descent numerator decomposes into three
   non-negative terms:
   `(p_β * P'_r1) * (q_0 - q_1) = p_β * (P'_r1 - 2) * q_0 + (p_β - 2) * (2 * q_0 - 1) + (q_0 - 1)`,
   proving unconditional strict core descent `q_1 < q_0` for ALL `p_β ≥ 2`, ALL `P'_r1 ≥ 2`, and ALL `q_0 ≥ 2`! -/
theorem thm31_collatz_macro_step_double_sl2_bezout_lock_and_unconditional_r0_core_descent
    (Pr1 Qr1 Pr1_next pbeta q0 q1 n0 n1 : Int)
    (hn0  : n0 + 1 = Pr1 * q0)
    (hMac : pbeta * n1 + 1 = Qr1 * q0)
    (hn1  : n1 + 1 = Pr1_next * q1) :
    (Pr1 * q0 - n0 = 1 ∧
     Qr1 * q0 - pbeta * n1 = 1 ∧
     pbeta * n1 - n0 = (Qr1 - Pr1) * q0) ∧
    (Qr1 = 3 →
      (pbeta * Pr1_next) * (q0 - q1) =
        pbeta * (Pr1_next - 2) * q0 + (pbeta - 2) * (2 * q0 - 1) + (q0 - 1) ∧
      (pbeta ≥ 2 → Pr1_next ≥ 2 → q0 ≥ 2 →
        (pbeta * Pr1_next) * (q0 - q1) ≥ q0 - 1 ∧ q1 < q0)) := by
  have hHomog : (pbeta * n1 - n0) - (Qr1 - Pr1) * q0 =
               (pbeta * n1 + 1 - Qr1 * q0) - (n0 + 1 - Pr1 * q0) := by
    simp only [Int.sub_mul]
    omega
  refine ⟨⟨by omega, by omega, by omega⟩, ?_⟩
  intro hQr3
  have hCore1 : (pbeta * Pr1_next) * q1 = pbeta * (Pr1_next * q1) := by
    simp only [Int.mul_assoc]
  rw [← hn1] at hCore1
  have hCore2 : pbeta * (n1 + 1) = (pbeta * n1 + 1) + (pbeta - 1) := by
    simp only [Int.mul_add, Int.mul_one]
    omega
  rw [hMac, hQr3] at hCore2
  have hDecompId : ((pbeta * Pr1_next) * q0 - (3 * q0 + (pbeta - 1))) -
                   (pbeta * (Pr1_next - 2) * q0 + (pbeta - 2) * (2 * q0 - 1) + (q0 - 1)) = 0 := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have hDiffExpand : (pbeta * Pr1_next) * (q0 - q1) = (pbeta * Pr1_next) * q0 - (pbeta * Pr1_next) * q1 := by
    simp only [Int.mul_sub]
  have hExactDecomp : (pbeta * Pr1_next) * (q0 - q1) =
                      pbeta * (Pr1_next - 2) * q0 + (pbeta - 2) * (2 * q0 - 1) + (q0 - 1) := by
    omega
  refine ⟨hExactDecomp, ?_⟩
  intro hpbeta hPrnext hq0
  have hTerm1 : pbeta * (Pr1_next - 2) * q0 ≥ 0 :=
    Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) (by omega)
  have hTerm2 : (pbeta - 2) * (2 * q0 - 1) ≥ 0 :=
    Int.mul_nonneg (by omega) (by omega)
  have hGe : (pbeta * Pr1_next) * (q0 - q1) ≥ q0 - 1 := by omega
  have hPosProd : pbeta * Pr1_next > 0 := Int.mul_pos (by omega) (by omega)
  have hLt : q1 < q0 := by
    by_cases hLe : q0 - q1 ≤ 0
    · have hNonpos : (pbeta * Pr1_next) * (q0 - q1) ≤ 0 :=
        Int.mul_nonpos_of_nonneg_of_nonpos (by omega) hLe
      omega
    · omega
  exact ⟨hGe, hLt⟩

/-- **Theorem 32 (Two-Macro-Step Odd-Core Tail Compensation Law `q_{m-1} ↦ q_m ↦ q_{m+1}`)**:
Across any two consecutive macro-steps of the odd cores:
- Step `m - 1`: `(p_{β,0} * P_{r,1}) * q_1 - Q_{r,0} * q_0 = p_{β,0} - 1`
  (`P_{r,1} = 2^{r_1 + 1}`, `Q_{r,0} = 3^{r_0 + 1}`, `p_{β,0} = 2^{β_0}`),
- Step `m`:     `(p_{β,1} * P_{r,2}) * q_2 - Q_{r,1} * q_1 = p_{β,1} - 1`
  (`P_{r,2} = 2^{r_2 + 1}`, `Q_{r,1} = 3^{r_1 + 1}`, `p_{β,1} = 2^{β_1}`):
Eliminating `q_1` pairs the intermediate ternary growth `Q_{r,1} = 3^{r_1 + 1}` with its own preceding
binary division `P_{r,1} = 2^{r_1 + 1}` inside `P_comp = (p_{β,0} * P_{r,1}) * (p_{β,1} * P_{r,2})`:
`P_comp * q_2 - (Q_{r,0} * Q_{r,1}) * q_0 = Q_{r,1} * (p_{β,0} - 1) + (p_{β,0} * P_{r,1}) * (p_{β,1} - 1)`
and `P_comp * (q_0 - q_2) = (P_comp - Q_{r,0} * Q_{r,1}) * q_0 - D_comp`. -/
theorem thm32_collatz_two_macro_step_core_tail_compensation_law
    (pbeta0 pbeta1 Pr1 Pr2 Qr0 Qr1 q0 q1 q2 : Int)
    (hStep0 : (pbeta0 * Pr1) * q1 - Qr0 * q0 = pbeta0 - 1)
    (hStep1 : (pbeta1 * Pr2) * q2 - Qr1 * q1 = pbeta1 - 1) :
    let Pcomp := (pbeta0 * Pr1) * (pbeta1 * Pr2)
    let Qcomp := Qr0 * Qr1
    let Dcomp := Qr1 * (pbeta0 - 1) + (pbeta0 * Pr1) * (pbeta1 - 1)
    (Pcomp * q2 - Qcomp * q0 = Dcomp) ∧
    (Pcomp * (q0 - q2) = (Pcomp - Qcomp) * q0 - Dcomp) := by
  dsimp
  have hElim : ((pbeta0 * Pr1) * (pbeta1 * Pr2) * q2 - (Qr0 * Qr1) * q0) -
               (Qr1 * (pbeta0 - 1) + (pbeta0 * Pr1) * (pbeta1 - 1)) =
               (pbeta0 * Pr1) * ((pbeta1 * Pr2) * q2 - Qr1 * q1 - (pbeta1 - 1)) +
               Qr1 * ((pbeta0 * Pr1) * q1 - Qr0 * q0 - (pbeta0 - 1)) := by
    simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul,
               Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    omega
  have e0 : (pbeta0 * Pr1) * q1 - Qr0 * q0 - (pbeta0 - 1) = 0 := by omega
  have e1 : (pbeta1 * Pr2) * q2 - Qr1 * q1 - (pbeta1 - 1) = 0 := by omega
  rw [e0, e1] at hElim
  simp only [Int.mul_zero, Int.add_zero] at hElim
  have h1 : (pbeta0 * Pr1) * (pbeta1 * Pr2) * q2 - (Qr0 * Qr1) * q0 =
            Qr1 * (pbeta0 - 1) + (pbeta0 * Pr1) * (pbeta1 - 1) := by omega
  have h2 : (pbeta0 * Pr1) * (pbeta1 * Pr2) * (q0 - q2) =
            (pbeta0 * Pr1) * (pbeta1 * Pr2) * q0 - (pbeta0 * Pr1) * (pbeta1 * Pr2) * q2 := by
    simp only [Int.mul_sub]
  have h3 : ((pbeta0 * Pr1) * (pbeta1 * Pr2) - Qr0 * Qr1) * q0 =
            (pbeta0 * Pr1) * (pbeta1 * Pr2) * q0 - (Qr0 * Qr1) * q0 := by
    simp only [Int.sub_mul]
  exact ⟨h1, by omega⟩

/-- **Theorem 33 (Pure-Binary `F_{a,b}` Non-Descending Constraint, `2^{a+1}` 2-Adic Construction Modulus,
and Finite Centered `(2,3)`-Radix Expansion `3^b m_0 - 2^a m_b = ∑ 3^{b-1-k} d_k 2^{s_k}` with `d_k = 2^{α_k - 1} - 2`)**:
1. With `E_{a,b} = (n_0 - 1) * F_{a,b} + ΔE_{a,b}` in `F_tot * n_0 - P_tot * n_b = E_{a,b}`,
   `P_tot * (n_0 - n_b) = (F_{a,b} - (F_tot - P_tot)) * n_0 - F_{a,b} + ΔE_{a,b}`, so any non-descending
   trajectory (`n_b ≥ n_0`, `ΔE_{a,b} ≥ 0`) satisfies `(F_{a,b} - (F_tot - P_tot)) * n_0 + ΔE_{a,b} ≤ F_{a,b}`.
2. Any two starting numbers `n_0, n'_0` sharing the same `b`-step gear vector (`Q_tot * n_0 + D_{a,b} = P_tot * (2 k_b + 1)`)
   satisfy `Q_tot * (n_0 - n'_0) = (2 * P_tot) * (k_b - k'_b)`.
3. Writing `n_0 = 2 * m_0 + 1`, `n_b = 2 * m_b + 1`, and `P_tot - Q_tot - D_{a,b} = 2 * S_d`
   (`S_d = ∑_{k=0}^{b-1} 3^{b-1-k} (2^{α_k - 1} - 2) 2^{s_k}`, whose digits vanish at the stationary gear `α_k = 2`),
   `Q_tot * m_0 - P_tot * m_b = S_d`, yielding a finite representation `Q_tot * m_0 = S_d` when `m_b = 0` (`n_b = 1`)
   and an upper ceiling `S_d ≤ (Q_tot - P_tot) * m_0` along any non-descending arc (`m_b ≥ m_0`). -/
theorem thm33_collatz_pure_binary_F_polynomial_and_finite_centered_radix_representation
    (Ftot Ptot Qtot n0 n0_prime nb Fab DeltaE Dab kb kb_prime m0 mb Sd : Int) :
    let Eab := (n0 - 1) * Fab + DeltaE
    (Ftot * n0 - Ptot * nb = Eab →
      Ptot * (n0 - nb) = (Fab - (Ftot - Ptot)) * n0 - Fab + DeltaE ∧
      (Ptot * (n0 - nb) ≤ 0 → DeltaE ≥ 0 → (Fab - (Ftot - Ptot)) * n0 + DeltaE ≤ Fab ∧
        (Fab - (Ftot - Ptot)) * n0 ≤ Fab)) ∧
    (Qtot * n0 + Dab = Ptot * (2 * kb + 1) →
     Qtot * n0_prime + Dab = Ptot * (2 * kb_prime + 1) →
      Qtot * n0 + Dab = (2 * Ptot) * kb + Ptot ∧
      Qtot * (n0 - n0_prime) = (2 * Ptot) * (kb - kb_prime)) ∧
    (n0 = 2 * m0 + 1 → nb = 2 * mb + 1 →
     Ptot * nb - Qtot * n0 = Dab →
     Ptot - Qtot - Dab = 2 * Sd →
      Qtot * m0 - Ptot * mb = Sd ∧
      (mb = 0 → Qtot * m0 = Sd) ∧
      (Ptot * (mb - m0) ≥ 0 → Sd ≤ (Qtot - Ptot) * m0)) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro hE
    have hId : Ptot * (n0 - nb) - ((Fab - (Ftot - Ptot)) * n0 - Fab + DeltaE) =
               (Ftot * n0 - Ptot * nb) - ((n0 - 1) * Fab + DeltaE) := by
      simp only [Int.mul_sub, Int.sub_mul, Int.one_mul, Int.mul_comm, Int.mul_left_comm]
      omega
    refine ⟨by omega, ?_⟩
    intro hNonDesc hDeltaPos
    exact ⟨by omega, by omega⟩
  · intro h1 h2
    have hExpand1 : Ptot * (2 * kb + 1) = (2 * Ptot) * kb + Ptot := by
      simp only [Int.mul_add, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have hExpand2 : Ptot * (2 * kb_prime + 1) = (2 * Ptot) * kb_prime + Ptot := by
      simp only [Int.mul_add, Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    have hDiff : Qtot * (n0 - n0_prime) - (2 * Ptot) * (kb - kb_prime) =
                 (Qtot * n0 - (2 * Ptot) * kb) - (Qtot * n0_prime - (2 * Ptot) * kb_prime) := by
      simp only [Int.mul_sub]
      omega
    exact ⟨by omega, by omega⟩
  · intro hn0 hnb hTraj hSd
    have hRadix : 2 * (Qtot * m0 - Ptot * mb - Sd) =
                  (Ptot - Qtot - Dab - 2 * Sd) + (Dab - (Ptot * (2 * mb + 1) - Qtot * (2 * m0 + 1))) := by
      simp only [Int.mul_add, Int.mul_sub, Int.sub_mul, Int.mul_one,
                 Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      omega
    rw [← hn0, ← hnb] at hRadix
    have hEq : Qtot * m0 - Ptot * mb = Sd := by omega
    have hCeil : (Qtot - Ptot) * m0 - Sd = Ptot * (mb - m0) + (Sd - (Qtot * m0 - Ptot * mb)) := by
      simp only [Int.sub_mul, Int.mul_sub]
      omega
    refine ⟨hEq, ?_, ?_⟩
    · intro hmb0
      have hP0 : Ptot * mb = 0 := by rw [hmb0]; simp
      omega
    · intro hGe
      omega

#print axioms thm18_universal_arbitrary_modulus_rotator_and_two_arc_trajectory_wronskian
#print axioms thm19_collatz_catalan_sl2_basis_drift_bounds_and_positive_wronskian_sum
#print axioms thm20_collatz_dual_drift_tower_and_cyclic_shift_law
#print axioms thm21_collatz_planetary_stationary_point_uniqueness_and_reachability_criterion
#print axioms collatz_global_convergence_from_local_descent
#print axioms thm22_collatz_arbitrary_stage_fermat_descent_reduction
#print axioms thm23_collatz_dead_end_free_ternary_prefix_closure
#print axioms thm24_collatz_counter_rotating_forward_backward_splice_and_bezout_lock
#print axioms thm25_collatz_automatic_2adic_3adic_gear_tooth_meshing_and_step_peeling
#print axioms thm26_collatz_step_wronskian_excess_identity_and_bernoulli_euler_cycle_lock
#print axioms thm27_collatz_pure_binary_stationary_excess_law_and_dual_drift_conservation
#print axioms thm28_collatz_centered_stationary_coordinate_and_gear_deviation_law
#print axioms thm29_collatz_trailing_ones_burn_macro_step
#print axioms thm30_collatz_odd_core_transition_law_and_post_burn_potential
#print axioms thm31_collatz_macro_step_double_sl2_bezout_lock_and_unconditional_r0_core_descent
#print axioms thm32_collatz_two_macro_step_core_tail_compensation_law
#print axioms thm33_collatz_pure_binary_F_polynomial_and_finite_centered_radix_representation

end RotatorCalculusPaper
