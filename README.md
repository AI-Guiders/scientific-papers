# Cuboctahedral Rotator Calculus in Lean 4

**On a Remarkable Property of the Cuboctahedral Rotator, Euler's Identity, and Closed-Form Evaluation of Fresnel, Jacobi, Bessel, and Dirichlet Integrals in Lean 4**  
*(Об одном замечательном свойстве кусочно-линейного ротатора на кубооктаэдре, тождестве Эйлера и замкнутом вычислении интегралов типа Френеля, Якоби, Бесселя и Дирихле)*

**Author:** Dmitrii A. Karataev (Д. А. Каратаев)  
**Formal Verification Partner:** Luch (Луч)  
**License:** Strong Reciprocal Copyleft — CC-BY-SA-4.0 (LaTeX manuscripts, documentation, and PDFs) / GPL-3.0-or-later (Lean 4 formalization code)

---

## Manuscript PDFs & Sources

- **English Preprint (PDF):** [`paper/paper-rotator-calculus-en.pdf`](paper/paper-rotator-calculus-en.pdf) ([LaTeX source](paper/paper-rotator-calculus-en.tex))
- **Russian Preprint (PDF):** [`paper/paper-rotator-calculus-ru.pdf`](paper/paper-rotator-calculus-ru.pdf) ([LaTeX source](paper/paper-rotator-calculus-ru.tex))
- **Self-Contained Lean 4 Formalization (604 lines, 0 external dependencies):** [`RotatorCalculusPaper.lean`](RotatorCalculusPaper.lean)

---

## Main Mathematical Results (Formally Verified in Lean 4)

Extending the piecewise-linear trigonometric framework studied by Thompson (`arXiv:1205.3814`), where piecewise derivatives lost the classical sine–cosine coupling at the four diamond corners and integral calculus remained open, this work establishes a closed-form trigonometric and integral calculus on the 3D Archimedean cuboctahedron `O₂ = {e ∈ {-1, 0, +1}³ | e_x² + e_y² + e_z² = 2}` (`12` vertices, `6` square faces, `8` triangular faces) and the associated discrete phase ring `ℤ_{512}` (quarter-period `Q_□ = 2^(8 - 1) = 128`, half-period `Φ_half = 256`, full period `N_ring = 512`, octant bisector step `K_P = 64`):

### 1. Theorem 1 (`thm1_constant_wronskian_weierstrass_lift_and_newton_leibniz`) — Discrete Euler Exponential, Euler's Identity `e^(iπ) + 1 = 0`, Constant Difference Wronskian, and Weierstrass Lift

- **Discrete Euler Exponential and Euler's Identity:**  
  The branchless projection pair `E₃(φ) = (C₃(φ), S₃(φ))` with `C₃(φ) = Q_□ - |wrap(φ)|` and `S₃(φ) = C₃(φ - Q_□)` satisfies quarter-turn multiplication by `i` (`E₃(φ + Q_□) = (-S₃(φ), C₃(φ))`) and half-turn Euler's identity across all 512 points of the ring:
  ```text
  E₃(φ + Φ_half) + E₃(φ) = (0, 0)      (e^(iπ) + 1 = 0)
  ```
- **Universal Constant Difference Wronskian:**  
  The one-step difference Wronskian is **identically constant across all 512 points of the ring**, including the four corner vertices:
  ```text
  W₃(φ) := C₃(φ) * S₃(φ + 1) - S₃(φ) * C₃(φ + 1)
          = <E₃(φ + Q_□), ΔE₃(φ)>  ≡  Q_□ = 128
  ```
- **Brahmagupta–Weierstrass Euclidean Lift & Discrete Newton–Leibniz Theorem:**  
  The polynomial lift `(X₃, Y₃, R₃) = (C₃² - S₃², 2 * C₃ * S₃, C₃² + S₃²)` satisfies `X₃(φ)² + Y₃(φ)² = R₃(φ)²` without square roots at all 512 points, and exact discrete Newton–Leibniz antiderivatives hold across the entire ring (`∑_{φ=0}^{255} S₃(φ) = Q_□² = 16,384`).

### 2. Theorem 2 (`thm2_closed_form_fresnel_jacobi_dirichlet_parseval_bessel_integrals`) — Closed-Form Evaluation of Non-Elementary Integrals

- **Lemniscate Jacobi Elliptic Triad `(sn₃, cn₃, dn₃)`:**  
  At the intrinsic cuboctahedron modulus `k² = 1 / ‖e‖₂² = 1/2`, the triad satisfies `|sn₃(φ)| + |cn₃(φ)| = Q_□` and `2 * dn₃(φ) + |sn₃(φ)| = Φ_half` across all 512 points, yielding closed-form complete and incomplete elliptic integrals of the second kind (`E_ell(3; 2, 3) = 163,840`).
- **Discrete Fresnel Diffraction Integrals:**  
  `C_Fresnel(3) = S_Fresnel(3) = 2048` via exact half-period cancellation of 480 oscillating quadratic residues and constructive survival of 32 stationary-phase points at the bisector `φ² ≡ K_P = 64 (mod 512)`.
- **Dirichlet Sine Integral, Parseval Energy Integral, and Zero-Order Bessel Integral:**  
  `Si₃(128) = Si₃(256) = 128`, `∑_{φ=0}^{511} C₃(φ)² = 2,796,288`, `J_{0,3}(0) = 65,536`, `J_{0,3}(1) = 32,768`, and the exact root `J_{0,3}(4) = 0`.

### 3. Theorem 3 (`thm3_continuum_integration_from_cuboctahedron_archimedes_layers`) — Archimedes Equizonal Partition, Continuum Riemann Integral, `π(n)` Rational Brackets, Calculator-Free Rational Trigonometry, and 3D Euler-Angle Rotator

- **Archimedes Equizonal Partition & 3D Continuum Riemann Integral:**  
  Projecting the 12 vertices of `O₂` onto any coordinate axis `e_x ∈ {-1, 0, +1}` yields the Archimedes equizonal partition `(4, 4, 4)`, which together with the central node of weight 12 derives Simpson's parabolic weights `(4, 16, 4) = 4 × (1, 4, 1)` and reproduces the exact 3D continuum Riemann integral `∭_{[-1,1]³} F dV`.
- **Wronskian-Cube Identity for `π(n)`:**
  ```text
  π_out(n) - π_in(n) = ∑_{j=0}^{n/2 - 1} W_s(j*s)³ / (I_s(j*s) * R₃(j*s) * R₃((j+1)*s)) > 0
  ```
  contracting by `4` at every polygon doubling (`π₃(16) = 142/45 = 3.1555…`, `π₃(512) = 3.141592667…`, giving 8 exact decimal digits of `π` in pure rationals).
- **Calculator-Free Verlet-Parabola Rational Sine (`verletParabolaSineRat`):**
  ```text
  sin_rat(p, q) = (4 * p * (2*q - p)) / (5 * q² - p * (2*q - p))
  ```
  evaluating `sin` and `cos` in two arithmetic operations and returning the exact structural ratios of the cuboctahedron `(17/97, 1/2, 12/17, 32/37, 1)` at `(10°, 30°, 45°, 60°, 90°)`.
- **Second-Moment Isotropy, Fourth-Moment Anisotropy Law, and 3D Euler-Angle Rotator:**
  ```text
  ∑_{e ∈ O₂} (k · e)² = 8 |k|²,       ∑_{e ∈ O₂} (k · e)⁴ = 12 |k|⁴ - 4 ∑_{i=1}^3 k_i⁴
  ```
  together with the root-free 3D Euler-angle rotator `R_Euler(φ₁, φ₂, φ₃)` across the `dim SO(3) = 3` equatorial squares `(xy, xz, yz)` of the cuboctahedron, preserving the exact spherical norm `‖R_Euler(φ₁, φ₂, φ₃) v‖₂² = (R₃(φ₁) R₃(φ₂) R₃(φ₃))² ‖v‖₂²`.

### 4. Theorem 4 (`thm4_boolean_post_completeness_3sat_reduction_and_channel_orthogonality`) — Post Functional Completeness `{NOT, XOR, OR, AND}`, Branchless 3-SAT Representation, `7 → 1` Remainder Gluing, and Two-Channel Non-Commutativity on `ℤ_{512}`

On the antipodal poles `{0, Φ_half} = {0, 256} ⊂ ℤ_{512}` (`C₃(0) = +128` encoding `True`, `C₃(256) = -128` encoding `False`), the rotator induces two canonical algebraic channels on triangular faces `(ψ₁, ψ₂, ψ₃) ∈ {0, 256}³`:
- **Channel 1 (Post's affine linear class `L` — pre-rotator phase addition):**  
  `NOT(ψ) = (ψ + 256) mod 512` (`C₃(ψ + 256) = -C₃(ψ)`) and 3-input `XOR` via `Q_□² * C₃(ψ₁ + ψ₂ + ψ₃) = C₃(ψ₁) * C₃(ψ₂) * C₃(ψ₃)`, with `256 + 256 ≡ 0 (mod 512)`.
- **Channel 2 (Non-linear threshold class — post-rotator projection sum with integer division by `512`):**
  ```text
  q_OR(ψ₁, ψ₂, ψ₃)  = tdiv(128 - (C₃(ψ₁) + C₃(ψ₂) + C₃(ψ₃)), 512) ∈ {0, 1}
  q_AND(ψ₁, ψ₂, ψ₃) = tdiv(128 + (C₃(ψ₁) + C₃(ψ₂) + C₃(ψ₃)), 512) ∈ {0, 1}
  ```
  By Turing–CA polynomial equivalence (`P_TM ≡ P_CA`, Cook–Levin), every Boolean circuit decomposes into Channel 1 and Channel 2, and a 3-SAT formula of `M` clauses is satisfiable iff `∑_{m=1}^M q_OR(ψ_{m,1}, ψ_{m,2}, ψ_{m,3}) = 0`.
- **Three Verified Algebraic Asymmetries Between Forward Verification (`NP`) and Inversion (`P`):**
  1. **Non-injective `7 → 1` remainder gluing:** `q_OR` discards the 3-valued remainder `r ∈ {-256, 0, +256}` and maps `7` distinct satisfying octants onto `q_OR = 0` (`1 → 7` preimage branching per clause).
  2. **Identical annihilation of Channel 2 linear gradients on Channel 1 parity constraints:** across the `4` clauses encoding a `3-XOR` parity equation, the sum of linear projections `C₃` vanishes identically on all `8` octants (`xor4LinearGradientSum ≡ 0`).
  3. **Non-distributivity and non-commutativity of Channel 1 and Channel 2:** `C₃(0 + 0) = 128 ≠ 256 = C₃(0) + C₃(0)` and `q_AND(0 + 0, 0, 0) = 1 ≠ 0 = (q_AND(0, 0, 0) + q_AND(0, 0, 0)) mod 2`.
  4. **Single-point depth-`T` inverse cone underdetermination (backward state inversion & single-sensor inverse wave scattering):** the `T`-th coordination shell contains `cuboctShellNodes(3, T) = 10 T² + 2` equidistant nodes, the cumulative cone volume `V_{O₂}(3, T) = cuboctBallNodes(3, T)` obeys `3 * V_{O₂}(3, T) = 10 T³ + 15 T² + 11 T + 3` (`V_{O₂}(3, 3) = 3 * 7² = 147`), Channel 2 gluing induces `preimageRayBranching(3, T) = 7^T` indistinguishable preimages per ray (`7³ = 343` at `T = 3`), and 4-clause parity loops (`xor4LinearGradientSum ≡ 0`) form zero-gradient cloaked kernels invisible to single-point linear probing.

### 5. Theorem 5 (`thm5_constructive_de_rham_cohomology_nilpotent_algebra_and_banach_tarski_free_measure`) — Constructive de Rham–Stokes–Gauss–Chern Cohomology (`d² ≡ 0`), Division-Free Linear Algebra, Variational `L¹` Saddle Optimization, and Banach–Tarski-Free Measure Additivity

Completes the five pillars of **100% Constructive Mathematics over `ℤ` and `ℚ` (`0 Classical.choice`, `0 sorryAx`)**:
- **Euclidean Connection Splitting & Variational `L¹` Saddle Law:**  
  Every difference `Δφ ∈ [-512, 512]` splits as `Δφ = 512 * q + r` (`q = branchQuot`, `r = edgeConn ∈ (-256, 256]`). Along `φ = 256 - k` (`k ∈ [0, 128]`), the conjugate projections `V(k) = |C₃(256 - k)| = 128 - k` and `I(k) = S₃(256 - k) = k` satisfy `V(k) + I(k) ≡ 128 = Q_□`, and their quadratic product `P(k) = V(k) * I(k) = (128 - k) * k` attains its unique maximum `P_max = K_P² = 64² = 4,096` at the Fresnel stationary phase `k* = 64`.
- **Constructive Stokes Theorem (`d₁ ∘ d₀ ≡ 0`) & Integer Chern Class Quantization:**  
  Around any closed 4-cycle face `f`, `(d₁(d₀φ))_f ≡ 0`, so the connection circulation is strictly quantized in multiples of `512`:
  ```text
  (d₁ r)_f  =  512 * n_f  ∈  512 ℤ,       n_f = -∑_{e ∈ ∂f} q_e ∈ ℤ
  ```
- **Constructive Gauss–Ostrogradsky Divergence Theorem (`d₂ ∘ d₁ ≡ 0`):**  
  Across the 6 square faces of a closed cube surface `∂□³`, the sum of oriented 2-cochain fluxes `(d₁ e)_f` vanishes identically for all integer edge 1-cochains `e₁..e₁₂ ∈ ℤ¹²`.
- **Division-Free Linear Algebra (`SL₂(ℤ)` & Nilpotent Neumann Inversion):**  
  The symplectic Verlet map `(u, v) ↦ (2u - v + Φ, u)` (`det = +1 ∈ SL₂(ℤ)`) inverts in place via `(u', v') ↦ (v', 2v' - u' + Φ)`, while the 4D nilpotent operator `M = I₄ + N_nil` (`N_nil³ = 0`, `det(2M) = 24`) inverts via the finite 3-term Neumann polynomial `M⁻¹ = I₄ - N_nil + N_nil²`.
- **Choice-Free, Banach–Tarski-Free Finite Measure Additivity:**  
  Without `Classical.choice`, every partition of the cuboctahedral ball `B_{O₂}(T)` into concentric coordination shells `10 k² + 2` strictly preserves integer volume `1 + ∑_{k=1}^T (10 k² + 2) = V_{O₂}(T)`, with `12 * (4² + 5²) = 492 > 256`.

### 6. Theorem 6 (`thm6_pillai_skeletal_matrix_decomposition_and_parabolic_sl2_jordan_triptych`) — Pillai Exponential Diophantine Skeletal Joint Matrix Decomposition, Parabolic `SL₂(ℤ)` Jordan Lock Triptych `k ∈ {6, 12, 15}`, Three-Level Recursive Descent Invariant, and Binomial Floor Divisibility Reciprocity

- **Skeletal Joint Matrix Factorization & Rank-1 Cross-Joint Transition Identity:**  
  Every solution of the exponential Diophantine equation `A x^m - B y^n = C` decomposes into `(m - 1)(n - 1)` interior `2 × 2` joint matrices `M_{a,b} = [[A x^(m-a), B y^(n-b)], [y^b, x^a]]` with invariant determinant `det M_{a,b} = C`. The normalized cross-joint transition matrix `P̃ = (1/C) M_{a,b}^adj M_{a',b'} ∈ SL₂(ℚ)` (`det P̃ = +1`) obeys the rank-1 decomposition:
  ```text
  P̃ - diag(y^Δb, x^Δa) = ((x^Δa y^Δb - 1) / C) * [[-x^a], [y^b]] * [[A x^(m-a'), B y^(n-b')]]
  ```
- **Parabolic Resonance Square Law & the `SL₂(ℤ)` Nilpotent Jordan Lock Triptych (`k ∈ {6, 12, 15}`):**  
  The parabolic boundary `Tr(P̃) = -2` (`(P̃ + I₂)² = 0`) is equivalent to the exact square identity `A x^(m-Δa) (x^Δa + 1)² = B y^(n-Δb) (y^Δb + 1)²`. For coprime bases (`A = B = 1`), integrality `P̃_k = [[-(k+1), -k], [k, k-1]] ∈ SL₂(ℤ)` reduces on interior elbows to `(x^a - x^Δa) + (y^b - y^Δb) = 2 s`, yielding the closed cuboctahedral triptych:
  1. **`k = 6` (`3² - 2³ = 1`, `C = 1`, square `6² = 36`):** `P̃_I = [[-7, -6], [6, 5]]` (`6` square faces of `O₂`),
  2. **`k = 12` (`2⁵ - 3³ = 5`, `C = 5`, square `12² = 144`):** `P̃_II = [[-13, -12], [12, 11]]` (`12` vertices of `O₂`),
  3. **`k = 15` (`5³ - 3⁴ = 44`, `C = 44`, square `30² = 900`, `s = 2`):** `P̃_III = [[-16, -15], [15, 14]]`.
- **Three-Level Recursive Descent Law & Floor `k = 2 ↔ k = 3` Binomial Divisibility Reciprocity:**  
  Along any skeletal ray `(k, j)`, consecutive floor differences `C_t = A x^(m - t k) - B y^(n - t j)` satisfy the weight-independent 3-term linear recurrence `C₀ - (x^k + y^j) C₁ + x^k y^j C₂ = 0` (forming the palindrome `(C₀, C₁, C₂) = (5, 7, 5)` on `2⁵ - 3³ = 5`), while the binomial divisibility laws `x^a | (B y^(r_y) (y^b - x^a)^k + C)` and `y^b | (A x^(r_x) (x^a - y^b)^k - C)` exhibit exact quotient reciprocity `(12, 4) ↔ (4, -12)` between floors `k = 2` and `k = 3` on `5³ - 3⁴ = 44`.

---

## Reproducing the Lean 4 Verification

Requires Lean 4 (tested with Lean 4.15+ / 4.36.0; zero external packages or Mathlib required):

```bash
lake build
lake env lean RotatorCalculusPaper.lean
```

Expected `#print axioms` output at the end of `RotatorCalculusPaper.lean`:
```text
'RotatorCalculusPaper.thm1_constant_wronskian_weierstrass_lift_and_newton_leibniz' depends on axioms: [propext]
'RotatorCalculusPaper.thm2_closed_form_fresnel_jacobi_dirichlet_parseval_bessel_integrals' depends on axioms: [propext]
'RotatorCalculusPaper.thm3_continuum_integration_from_cuboctahedron_archimedes_layers' depends on axioms: [propext]
'RotatorCalculusPaper.thm4_boolean_post_completeness_3sat_reduction_and_channel_orthogonality' depends on axioms: [propext]
'RotatorCalculusPaper.thm5_constructive_de_rham_cohomology_nilpotent_algebra_and_banach_tarski_free_measure' depends on axioms: [propext]
'RotatorCalculusPaper.thm6_pillai_skeletal_matrix_decomposition_and_parabolic_sl2_jordan_triptych' depends on axioms: [propext]
```
(`0 sorryAx`, `0 Classical.choice`).
