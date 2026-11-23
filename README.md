# AI-Guiders Scientific Papers & Formal Lean 4 Verifications

**Series I: Constructive Cuboctahedral Rotator Calculus on `ℤ_{512}`, Closed-Form Quadrature, Finite-State Adversary Barriers, and Root-Free Diophantine Padé–Bézout–Wronskian Identities in Lean 4**  
*(Серия I: Конструктивное ротаторное исчисление на кубооктаэдре и кольце `ℤ_{512}`, замкнутые квадратуры, барьеры конечных вычислителей и бескорневые диофантовы тождества Паде–Безу–Вронскиана в Lean 4)*

**Author:** Dmitrii A. Karataev (Д. А. Каратаев)  
**Formal Verification Partner:** Luch (Луч)  
**License:** Strong Reciprocal Copyleft — CC-BY-SA-4.0 (LaTeX manuscripts, documentation, and PDFs) / GPL-3.0-or-later (Lean 4 formalization code)

---

## Paper Catalog: Two Trunks — Pure Mathematics (`mathematics/`) & Unified Natural Science (`theory/`, `laboratory/`, `engineering/`)

In this framework, abstract Computer Science (Boolean Post completeness, 3-SAT phase reduction, cohomology, and the Lawvere–Gödel–Tarski diagonal theorem) belongs to **Pure Mathematics (`mathematics/`)**, whereas physics, chemistry, molecular biology, cosmology, and the physical realization of computation in hardware collapse back into a **single unified Natural Science (*Естествознание*)** governed by Discrete Quantum Mechanics (DQM, $1 + 2^3 = 3^2$, $\mathbb{Z}_{512}$, $O_2(3)$) and organized by operational role into **`theory/`**, **`laboratory/`**, and **`engineering/`**.

### I. Pure Mathematics & Abstract Computer Science (`mathematics/`)

| Topic & Standalone Lean 4 Module | Standalone Paper Title & Verified Lean 4 Theorems | English PDF & TeX | Russian PDF & TeX |
| :--- | :--- | :--- | :--- |
| **1. Core Apparatus** · [`RotatorQuadrature.lean`](RotatorQuadrature.lean) | **Cuboctahedral Rotator Calculus: Discrete Euler Exponential on `ℤ_{512}` & `ℤ_{4Q}`, Universal Constant Wronskian `W ≡ Q`, and Closed-Form Quadrature on `O₂(3)`** (`thm1`, `thm2`, `thm3`) | [PDF](mathematics/rotator-quadrature-en.pdf) · [TeX](mathematics/rotator-quadrature-en.tex) | [PDF](mathematics/rotator-quadrature-ru.pdf) · [TeX](mathematics/rotator-quadrature-ru.tex) |
| **2. Logic, Cohomology & Barriers** · [`LogicCohomology.lean`](LogicCohomology.lean) | **Post Functional Completeness, 3-SAT Phase-Polynomial Reduction, Constructive de Rham Cohomology, and Finite-State Adversary Barriers / Built-In Vernam Pad on `ℤ_{512}`** (`thm4`, `thm5`) | [PDF](mathematics/logic-cohomology-barriers-en.pdf) · [TeX](mathematics/logic-cohomology-barriers-en.tex) | [PDF](mathematics/logic-cohomology-barriers-ru.pdf) · [TeX](mathematics/logic-cohomology-barriers-ru.tex) |
| **3. Pillai's Problem (`A x^m - B y^n = C`)** · [`PillaiDiophantine.lean`](PillaiDiophantine.lean) | **Exponential Diophantine Equations `A x^m - B y^n = C` (Pillai's Problem): Root-Free Integer Padé–Thue Compression, Isotropic Cone Matrix Decomposition, and Parabolic `SL₂(ℤ)` Jordan Locks `k ∈ {6, 12, 15, 40}`** (`thm6`, `thm7`, `thm10`, `thm11`) | [PDF](mathematics/pillai-exponential-diophantine-en.pdf) · [TeX](mathematics/pillai-exponential-diophantine-en.tex) | [PDF](mathematics/pillai-exponential-diophantine-ru.pdf) · [TeX](mathematics/pillai-exponential-diophantine-ru.tex) |
| **4. `abc` Triples (`A + B = C`)** · [`AbcPlanetaryWronskian.lean`](AbcPlanetaryWronskian.lean) | **Planetary Differential Geometry of Coprime Triples `A + B = C` (`abc` Triples): Integer Mason–Stothers–Bézout Wronskians, Circle-Remainder Degree Reduction, Cross-Floor Genus-10 Lock, and Stereographic `ℤ_{512}` Embedding** (`thm8`, `thm9`, `thm12`–`thm16`) | [PDF](mathematics/abc-planetary-differential-wronskian-en.pdf) · [TeX](mathematics/abc-planetary-differential-wronskian-en.tex) | [PDF](mathematics/abc-planetary-differential-wronskian-ru.pdf) · [TeX](mathematics/abc-planetary-differential-wronskian-ru.tex) |
| **5. Collatz Problem (`2^a n_final - 3^b n_start = D`)** · [`CollatzPlanetarySplice.lean`](CollatzPlanetarySplice.lean) | **Collatz Trajectory Dynamics on Natural Modular Rings `ℤ_{2^a}`, `ℤ_{3^b}`, and `ℤ_{2^a - 3^b}`: `SL₂(ℤ)` Catalan Basis, Counter-Rotating Forward–Backward Gear Splice, Automatic `2`-adic/`3`-adic Tooth Meshing, and `2^a`-Free Bernoulli–Euler Drift Bounds** (`thm18`–`thm26`) | [PDF](mathematics/collatz-natural-ring-wronskian-en.pdf) · [TeX](mathematics/collatz-natural-ring-wronskian-en.tex) | [PDF](mathematics/collatz-natural-ring-wronskian-ru.pdf) · [TeX](mathematics/collatz-natural-ring-wronskian-ru.tex) |
| **Omnibus Math Reference** · [`RotatorCalculusPaper.lean`](RotatorCalculusPaper.lean) | **Combined Pure-Math Preprint & Umbrella Lean 4 Module** | [PDF](mathematics/rotator-calculus-omnibus-en.pdf) · [TeX](mathematics/rotator-calculus-omnibus-en.tex) | [PDF](mathematics/rotator-calculus-omnibus-ru.pdf) · [TeX](mathematics/rotator-calculus-omnibus-ru.tex) |

### II. Unified Natural Science under Discrete Quantum Mechanics (`theory/`, `laboratory/`, `engineering/`)

| Division, Topic & Lean 4 Module | Standalone Paper Title & Verified Lean 4 Modules (`AI-Guiders/discrete-quantum-mechanics`) | English PDF & TeX | Russian PDF & TeX |
| :--- | :--- | :--- | :--- |
| **`theory/` — 1. Foundations of DQM, Maxwell & `α_fs⁻¹`** | **Foundations of Discrete Quantum Mechanics (DQM): Dimensional Uniqueness `1 + 2^d = d²` (`d = 3`), Symplectic Verlet Dynamics on `ℤ_{512}`, Born's Rule, Heisenberg Deadband `41`, and the Fine-Structure Constant `α_fs⁻¹`** (`Core.lean`, `Dynamics.lean`, `Topology.lean`, `Physics.lean`) | [PDF](theory/dqm-foundations-maxwell-fine-structure-en.pdf) · [TeX](theory/dqm-foundations-maxwell-fine-structure-en.tex) | [PDF](theory/dqm-foundations-maxwell-fine-structure-ru.pdf) · [TeX](theory/dqm-foundations-maxwell-fine-structure-ru.tex) |
| **`theory/` — 2. Gravity, `16/3` Halo & `587×` Nuclear Collapse** | **Non-Singular Gate-Impedance Gravity (`≥ 8,192`), the `16/3` Vacuum Holonomy Halo Without Dark Matter, and Coherent `587×` Coulomb Barrier Collapse to the `N = 184` Island of Stability** (`Dynamics.lean`, `Physics.lean`, `UnifiedOperators.lean`) | [PDF](theory/gravity-halo-nuclear-collapse-en.pdf) · [TeX](theory/gravity-halo-nuclear-collapse-en.tex) | [PDF](theory/gravity-halo-nuclear-collapse-ru.pdf) · [TeX](theory/gravity-halo-nuclear-collapse-ru.tex) |
| **`theory/` — 3. Model-Theoretic Limit & Gödel–Tarski Oracle** · [`ModelTheoreticLimit.lean`](ModelTheoreticLimit.lean) | **Model-Theoretic Termination of the Physical Approximation Chain `T → {M_n}` (`lim M_n = M`), Bilateral Closure `⟨M, T⟩`, Constructive Impossibility of Contradiction (`0 Classical.choice`), and the Gödel–Tarski Necessity of Experimental Arbitration** (`thm17` in [`ModelTheoreticLimit.lean`](ModelTheoreticLimit.lean), `UnifiedOperators.lean`) | [PDF](theory/model-theoretic-limit-godel-arbitration-en.pdf) · [TeX](theory/model-theoretic-limit-godel-arbitration-en.tex) | [PDF](theory/model-theoretic-limit-godel-arbitration-ru.pdf) · [TeX](theory/model-theoretic-limit-godel-arbitration-ru.tex) |
| **`laboratory/` — 4. Cleanroom Silicon Photovoltaics Protocol** | **Impedance-Matched Phonon-Free Singlet-Fission Silicon Photovoltaics (`441 nm → 2 × 882 nm < 1,107 nm`), Step-by-Step Cleanroom Fabrication, A/B Falsification (`M1`–`M4`) & Troubleshooting Matrix (`F1`–`F6`)** (`UnifiedOperators.lean`, [`RotatorQuadrature.lean`](RotatorQuadrature.lean)) | [PDF](laboratory/phonon-free-silicon-photovoltaics-en.pdf) · [TeX](laboratory/phonon-free-silicon-photovoltaics-en.tex) | [PDF](laboratory/phonon-free-silicon-photovoltaics-ru.pdf) · [TeX](laboratory/phonon-free-silicon-photovoltaics-ru.tex) |
| **`engineering/` — 5. Phase-Relay Electrical & Silicon Engineering** · [`LogicCohomology.lean`](LogicCohomology.lean) | **Applied Engineering of DQM: Phase-Relay Electrical Engineering (`V = C₃, I = S₃`), Ripple-Free Quadrature Rectifiers, Physical Landauer-Free Computing, and Branchless Silicon Architecture (`Ring9 / Bus36 / VerletCell72`)** (`thm5` in [`LogicCohomology.lean`](LogicCohomology.lean), `UnifiedOperators.lean`) | [PDF](engineering/dqm-electrical-engineering-and-silicon-hardware-en.pdf) · [TeX](engineering/dqm-electrical-engineering-and-silicon-hardware-en.tex) | [PDF](engineering/dqm-electrical-engineering-and-silicon-hardware-ru.pdf) · [TeX](engineering/dqm-electrical-engineering-and-silicon-hardware-ru.tex) |

- **Modular Paper-by-Paper Lean 4 Formalization (6 standalone modules + umbrella [`RotatorCalculusPaper.lean`](RotatorCalculusPaper.lean), 26 theorems `thm1`–`thm26`, 0 external dependencies, `0 sorryAx`, `0 Classical.choice`):**
  1. [`RotatorQuadrature.lean`](RotatorQuadrature.lean) (`thm1`–`thm3`)
  2. [`LogicCohomology.lean`](LogicCohomology.lean) (`thm4`–`thm5`)
  3. [`PillaiDiophantine.lean`](PillaiDiophantine.lean) (`thm6`, `thm7`, `thm10`, `thm11`)
  4. [`AbcPlanetaryWronskian.lean`](AbcPlanetaryWronskian.lean) (`thm8`, `thm9`, `thm12`–`thm16`)
  5. [`ModelTheoreticLimit.lean`](ModelTheoreticLimit.lean) (`thm17`)
  6. [`CollatzPlanetarySplice.lean`](CollatzPlanetarySplice.lean) (`thm18`–`thm26` & `collatz_global_convergence_from_local_descent`)

### Companion Repositories in the `AI-Guiders` Ecosystem

| Repository | Role & Contents |
| :--- | :--- |
| [`AI-Guiders/scientific-papers`](https://github.com/AI-Guiders/scientific-papers) | Series I (`paper-1`..`paper-4`) & Series II (`paper-5`..`paper-8`) LaTeX/PDF papers and standalone [`RotatorCalculusPaper.lean`](RotatorCalculusPaper.lean) (`thm1`–`thm17`). |
| [`AI-Guiders/discrete-quantum-mechanics`](https://github.com/AI-Guiders/discrete-quantum-mechanics) | Full 8-chapter academic monograph, natural sciences course, `lean/MtCarrier/` formalization (`26/26` modules), and Python/Verilog verification suites. |
| [`AI-Guiders/guiders-physics`](https://github.com/AI-Guiders/guiders-physics) | `.NET` digital twin, interactive impedance simulator, and hardware telemetry engine. |
| [`AI-Guiders/ai-welcome-atlas`](https://github.com/AI-Guiders/ai-welcome-atlas) & [`AI-Guiders/ai-atlas-mcp`](https://github.com/AI-Guiders/ai-atlas-mcp) | Open Knowledge Format (OKF) knowledge base (`ai-welcome-atlas`) and anti-confabulation `.NET 11` MCP server (`ai-atlas-mcp`) enforcing tool-first verification (`0 sorryAx`, `0 Classical.choice`) and preventing LLM hallucination during scientific research and experimental troubleshooting. |

> **Model-Theoretic Terminology (A. I. Mal'cev, *Algebraic Systems*):**  
> Throughout this work, the term **"carrier"** (*«носитель»*) is used strictly in its standard model-theoretic sense (A. I. Mal'cev, *Algebraic Systems*, Nauka, 1970 / Springer-Verlag, 1973): the underlying domain set of a sort in a two-sorted algebraic structure `⟨M, T; π_{M→T}, ι_{T→M}⟩`, where the **discrete `M`-carrier** is the finite modular phase ring `ℤ_{512}` on the cuboctahedral lattice `ℤ³` (`L¹` diamond projections `C₃, S₃`) and the **continuous `T`-carrier** is the continuum sort of Euclidean circle invariants (`X² + Y² = R²`), rational/real projective coordinates `ℚ ⊂ ℝ`, and continuum Riemann integrals.

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

### 6. Theorem 6 (`thm6_pillai_skeletal_matrix_decomposition_and_parabolic_sl2_jordan_triptych`) — Pillai Skeletal Joint Matrix Decomposition, Isotropic Discriminant Cone Generators, Exact Generator Factorization `C = (x^(m-a) ∓ y^b)(x^a - y^b)`, and Parabolic `SL₂(ℤ)` Jordan Lock Quartet `k ∈ {6, 12, 15, 40}`

- **Skeletal Joint Matrix Factorization & Rank-1 Cross-Joint Transition Identity:**  
  Every solution of the exponential Diophantine equation `A x^m - B y^n = C` decomposes into `(m - 1)(n - 1)` interior `2 × 2` joint matrices `M_{a,b} = [[A x^(m-a), B y^(n-b)], [y^b, x^a]]` with invariant determinant `det M_{a,b} = C`. The normalized cross-joint transition matrix `P̃ = (1/C) M_{a,b}^adj M_{a',b'} ∈ SL₂(ℚ)` (`det P̃ = +1`) obeys the rank-1 decomposition:
  ```text
  P̃ - diag(y^Δb, x^Δa) = ((x^Δa y^Δb - 1) / C) * [[-x^a], [y^b]] * [[A x^(m-a'), B y^(n-b')]]
  ```
- **Isotropic Discriminant Cone Generators, Exact Generator Factorization, & the `SL₂(ℤ)` Nilpotent Jordan Lock Quartet (`k ∈ {6, 12, 15, 40}`):**  
  In quadric coordinates `X = (P̃₁₁ - P̃₂₂)/2`, `Y = (P̃₁₂ + P̃₂₁)/2`, `T = (P̃₁₂ - P̃₂₁)/2`, the characteristic discriminant is `(Tr(P̃)² - 4)/4 = X² + Y² - T²`. On symmetric elbows (`m = a + a'`, `n = b + b'`, `A = B = 1`), `Y ≡ 0`, the linear generator (ruling) `X - T` obeys `2 C (X - T) = (x^a - y^b)² - (x^a' - y^b')²`, and `y^b (x^(m-a) - y^(n-b)) + x^(m-a) (x^a - y^b) = C` yields the exact generator factorization `C = (x^(m-a) ∓ y^b)(x^a - y^b)` along the isotropic cone `X² - T² = 0` (`Tr(P̃) = ∓2`). For coprime bases, integrality `P̃_k ∈ SL₂(ℤ)` generates the closed quartet:
  1. **`k = 6` (`3² - 2³ = 1 = 1 × 1`, `C = 1`, square `6² = 36`, `Tr = -2`):** `P̃_I = [[-7, -6], [6, 5]]` (`6` square faces of `O₂`),
  2. **`k = 12` (`2⁵ - 3³ = 5 = 5 × 1`, `C = 5`, square `12² = 144`, `Tr = -2`):** `P̃_II = [[-13, -12], [12, 11]]` (`12` vertices of `O₂`),
  3. **`k = 15` (`5³ - 3⁴ = 44 = 22 × 2`, `C = 44`, square `30² = 900`, `s = 2`, `Tr = -2`):** `P̃_III = [[-16, -15], [15, 14]]`,
  4. **`k = 40` (`2¹⁰ - 5⁴ = 399 = 133 × 3`, `C = 399`, difference resonance `2⁷ - 2³ = 5³ - 5¹ = 120 = 5!`, `Tr = +2`, `(P̃_IV - I₂)² = 0`):** `P̃_IV = [[-39, -40], [40, 41]]` (`41 = 4² + 5²`), lying on the isotropic cone generator `X² - T² = (-40)² - (-40)² = 0`.

### 7. Theorem 7 (`thm7_pillai_recursive_descent_hankel_wronskian_farey_bezout_and_pade_thue_tower`) — Three-Level Recursive Descent Invariant, Hankel–Wronskian Square Law, Floor `k = 2 ↔ k = 3` Binomial Divisibility Reciprocity, Unimodular Farey–Bézout Exponent Matrix, and Padé–Thue Wronskian Tower

- **Unimodular Farey–Bézout Exponent Matrix & Base Reconstruction:**  
  For coprime exponents `gcd(m, n) = 1`, the canonical Farey–Bézout parent joints `(a, b)` and `(a', b') = (m - a, n - b)` form `E_Bezout = [[a, b], [a', b']] ∈ SL₂(ℤ)` (`a b' - a' b = +1`), reconstructing the bases via `(x^a)^b' = x * (x^a')^b` and `(y^b')^a = y * (y^b)^a'`.
- **Three-Level Recursive Descent Law, Hankel–Wronskian Identity, & Floor `k = 2 ↔ k = 3` Binomial Divisibility Reciprocity:**  
  Along any skeletal ray `(k, j)`, consecutive floor differences `C_t = A x^(m - t k) - B y^(n - t j)` satisfy the weight-independent 3-term linear recurrence `C₀ - (x^k + y^j) C₁ + x^k y^j C₂ = 0` and the Hankel–Wronskian square identity `C₁² - C₀ C₂ = A B x^(m - 2k) y^(n - 2j) (x^k - y^j)²` (forming the palindrome `(C₀, C₁, C₂) = (5, 7, 5)` with `7² - 5² = 24` on `2⁵ - 3³ = 5`), while the binomial divisibility laws `x^a | (B y^(r_y) (y^b - x^a)^k + C)` and `y^b | (A x^(r_x) (x^a - y^b)^k - C)` exhibit exact quotient reciprocity `(12, 4) ↔ (4, -12)` between floors `k = 2` and `k = 3` on `5³ - 3⁴ = 44`.
- **Non-Singular Padé–Thue Wronskian Tower, Cross-Floor Wronskian `W_{2,3}`, & Root-Free `9`-Cell Collision Laws:**  
  Exponent pairs `(m, n)` partition modulo `d = 3` into `d² = 9` residue cells `(m mod 3, n mod 3) ∈ {0, 1, 2}²`, reducing on each cell to `Ã X³ - B̃ Y³ = C` (`U = Ã X³`, `V = B̃ Y³`). The homogeneous integer Padé polynomials `P̂₁ = U + 2V`, `P̂₂ = 5U² + 35UV + 14V²`, `P̂₃ = 2U³ + 30U²V + 42UV² + 7V³` (with coefficient sums `1, 3, 54, 81 = 3⁴`) form `2 × 2` Wronskian matrices `M_N = [[X_N, Y_N], [X_{N+1}, Y_{N+1}]]` (`X_N = X P̂_N`, `Y_N = Y Q̂_N`) with exact determinants `det M_N = -(3N + 1) X Y C^(2N+1)` (multipliers `(1, 4, 7)` for `N = 0, 1, 2`). For any second point `(X', Y')` in the same cell (`Ã(X')³ - B̃(Y')³ = C'`), the integer collision invariants `I_N = Y' X_N - X' Y_N` satisfy the root-free Cramer lower-bound law `Y_{N+1} I_N - Y_N I_{N+1} = (3N + 1) X Y Y' C^(2N+1) ≠ 0` (`max(|I_N|, |I_{N+1}|) ≥ 1`) and the root-free cubic compression law `Ã I_N Φ₃(Y' X_N, X' Y_N) = (Y')³ C^(2N+1) R_N(U, V) - C' Y_N³`. Coupling the quadratic floor `k = 2` (`P̂_{1,2} = U + 3V`, `Q̂_{1,2} = 3U + V`) and the cubic floor `k = 3` (`P̂_{1,3} = U + 2V`, `Q̂_{1,3} = 2U + V`) of a single solution `(U, V)` yields `(U + V) P̂_{1,2}² - P̂_{1,3}³ = V(U² + 3UV + V²)`, `(U + V) Q̂_{1,2}² - Q̂_{1,3}³ = U(U² + 3UV + V²)`, and the cross-floor Wronskian `det W_{2,3} = Q̂_{1,2}² P̂_{1,3}³ - P̂_{1,2}² Q̂_{1,3}³ = C³(U² + 3UV + V²)` (`det W_{2,3}(9, 8) = 361 = 19²` on Lock I).

### 8. Theorem 8 (`thm8_unified_3x3_pillai_abc_skeletal_matrix_and_radical_floor_embedding`) — Radical-Bounded Skeletal Floor Embedding of `abc`-Triples, Unified Bordered `3 × 3` Pillai–`abc` Matrix `M₃`, Three-Channel `3 × 3` Cubic Padé Matrix `P₃(A, B, C)`, and Bilateral Carrier Isomorphism (`M ⇄ T`)

- **Radical-Bounded Skeletal Floor Embedding of `abc`-Triples:**  
  Every coprime triple `A + B = C` (`gcd(A, B, C) = 1`) decomposes on floor `k ≥ 2` into `Ã_k X_k^k + B̃_k Y_k^k = C̃_k Z_k^k` with root weights bounded by the radical: `Ã_k B̃_k C̃_k ≤ rad(A B C)^(k-1)` (on the Lock IV top-floor triple `3 + 5³ = 2⁷ = 128` with `rad = 2 * 3 * 5 = 30`, floor `k = 3` yields `3 * 1³ + 1 * 5³ = 2 * 4³ = 128` with `Ã₃ B̃₃ C̃₃ = 6 ≤ 30²` and shaft gap `5 - 4 = 1`).
- **Unified Bordered `3 × 3` Pillai–`abc` Matrix `M₃`, Three-Channel `3 × 3` Padé Matrix `P₃(A, B, C)`, & Bilateral Carrier Transfer Isomorphism (`M ⇄ T`):**  
  For any factorization `A = a₁ a₂`, `B = b₁ b₂`, `C = c₁ c₂` with `A + B = C`, the bordered `3 × 3` matrix `M₃ = [[c₂, a₂, b₂], [a₁, c₁, 0], [b₁, 0, c₁]]` has `det M₃ = c₁ (C - A - B) ≡ 0`, principal `2 × 2` minors `(B, A, c₁²)`, and rank-1 adjugate `M₃^adj = [c₁, -a₁, -b₁]^T [c₁, -a₂, -b₂]` satisfying `(M₃^adj)² = (c₁² + C) M₃^adj` (`Tr(M₃^adj) = 4² + 128 = 144 = 12²` on `3 + 5³ = 2⁷ = 128`), while the lower and upper triangle defects `Δ_low = c₁ - (a₁ + b₁)` and `Δ_high = c₂ - (a₂ + b₂)` obey `(a₁ + b₁) Δ_high + c₂ Δ_low = -(a₁ b₂ + a₂ b₁) < 0`. Combining the three cubic Padé channels of `A + B = C` forms the singular `3 × 3` matrix `P₃(A, B, C) = [[A²(B+C), (B+2C)³, (2B+C)³], [(A+2C)³, B²(A+C), (2A+C)³], [(A-2B)³, (2A-B)³, C²(A-B)]]` with universal kernel `P₃(A, B, C) [A, B, -C]^T = [0, 0, 0]`, `det P₃(A, B, C) = 0`, and trace `Tr(P₃(A, B, C)) = A C (A + C)` (`Tr(P₃(3, 125, 128)) = 3 * 128 * 131 = 50,304`), while the base `7 = |△(3)| - 1` links the Padé coefficient sum `P̂₃(1, 1) = 81 = 3⁴` and the phase ring modulus `|ℤ_{512}| = 512 = 2⁹` via the dual Fermat–Catalan identities `2⁵ + 7² = 3⁴ = 81` and `13² + 7³ = 2⁹ = 512`. Across all `512` states of `ℤ_{512}`, the forward Weierstrass lift `π_{M→T}(C, S) = (X₃, Y₃, R₃) = (C² - S², 2CS, C² + S²)` from the discrete `L¹`-carrier `M` to the continuous Euclidean circle `T` (`X₃² + Y₃² = R₃²`) obeys `R₃(φ) + |Y₃(φ)| ≡ Q_□(3)² = 16,384` (`128 | X₃(φ)`), inverts without square roots via `ι_{T→M}(X₃) = ((16,384 + X₃)/256, (16,384 - X₃)/256) ≡ (|C₃(φ)|, |S₃(φ)|)`, and induces the stereographic Weierstrass homeomorphism `[0, 512]/512 = [0, 1] ≅ ℝ` via `Y₃ / (R₃ + X₃) ≡ S₃ / C₃ = φ / (128 - |φ|)`.

- **Planetary Differential 3D Orthogonal Frame `F₃`, Gear-Slip Brahmagupta Law, Non-Singular Hankel–Vandermonde Matrix `H₃`, Lagrange–Vandermonde Shaft-Gap Projectors, & Bézout–Gauss Shell Inversion `K_Bezout`:**  
  For any planetary differential `A + B = C` (`A = a₁ a₂`, `B = b₁ b₂`, `C = c₁ c₂`), the gear-radius vector `r = (a₁, b₁, c₁) ∈ ℤ³` and turn-count vector `ω = (a₂, b₂, -c₂) ∈ ℤ³` are strictly orthogonal (`r · ω = A + B - C = 0`) and together with the satellite normal `n = r × ω = (-M_{BC}, M_{CA}, S_{AB})` (`M_{BC} = b₁ c₂ + b₂ c₁`, `M_{CA} = c₁ a₂ + c₂ a₁`, `S_{AB} = a₁ b₂ - a₂ b₁`, `M_{AB} = a₁ b₂ + a₂ b₁`) form an orthogonal `3 × 3` frame `F₃` with `det F₃ = M_{BC}² + M_{CA}² + S_{AB}² ≡ (a₁² + b₁² + c₁²)(a₂² + b₂² + c₂²) > 0` and planar gear-slip law `C² + S_{AB}² = (A - B)² + M_{AB}² ≡ (a₁² + b₁²)(a₂² + b₂²)` (where `S_{AB} = 0` for `gcd(A, B) = 1` occurs solely at the Pell square degeneracy `(m, n) = (2, 2)`; on `3 + 5³ = 2⁷ = 128`, `‖r‖₂² = 1² + 5² + 4² = 42 = S₂(3)`, `S_{AB} = 10`, `M_{AB} = 40 = k_IV`, and `M_{CA} = 44 = C_III`). On the cubic floor `k = 3` (`S_m = Ã X^m + B̃ Y^m - C̃ Z^m`, `S₃ = 0`), the `3 × 3` Hankel moment matrix `H₃ = [[S₀, S₁, S₂], [S₁, S₂, 0], [S₂, 0, S₄]]` obeys `-det H₃ = S₂³ - S₄(S₀ S₂ - S₁²) ≡ Ã B̃ C̃ (X - Y)² (Y - Z)² (Z - X)² > 0` (`S₁ = S₃ = 0` and `-det H₃ = 6 × 12² = 864` on `3 + 5³ = 2⁷ = 128`) and the three Lagrange–Vandermonde shaft-gap projectors `Ã X(X - Y)(X - Z) ≡ S₁ YZ - S₂(Y + Z)`, `B̃ Y(Y - X)(Y - Z) ≡ S₁ ZX - S₂(Z + X)`, and `C̃ Z(Z - X)(Z - Y) ≡ S₂(X + Y) - S₁ XY` (`max(|S₁|, |S₂|) ≥ 1` for distinct shafts `X, Y, Z`). Finally, coprimality `gcd(A, B, C) = 1` defines a unique conjugate Bézout partner triple `u + v = w` (`0 ≤ u < A`, `0 < v ≤ B`, `0 < w < C`) forming `B_{2×3} = [[A, B, C], [u, v, w]]` with all three `2 × 2` minors equal to `+1` (`Av - Bu = Aw - Cu = Cv - Bw = +1`; yielding `(u, v, w) = (2, 11, 13)` on `5 + 27 = 32` and `(1, 42, 43)` on `3 + 125 = 128` with `v = 42 = ‖r‖₂²`), while the shaft-Bézout parent `(w₃, v₃)` of `(Z₃, Y₃)` (`Z₃ v₃ - Y₃ w₃ = +1`, `A' = C̃₃ w₃³ - B̃₃ v₃³`) forms the cube matrix `K_Bezout = [[w₃³, -Z₃³], [v₃³, -Y₃³]]` with Gauss-shell determinant `det K_Bezout = (Y₃ w₃ + 1)³ - (Y₃ w₃)³ = Φ₃(Z₃ v₃, Y₃ w₃) > 0` reconstructing the radical-bounded weights via `K_Bezout [A, A']^T = Φ₃(Z₃ v₃, Y₃ w₃) [B̃₃, C̃₃]^T` (`det K_Bezout = 4³ - 3³ = 37` on Lock II, and level-1 collision invariant `I₁ = (C + 2B) - A Y₃ w₃ = 333 = 9 × 37` on Lock IV).

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
'RotatorCalculusPaper.thm7_pillai_recursive_descent_hankel_wronskian_farey_bezout_and_pade_thue_tower' depends on axioms: [propext]
'RotatorCalculusPaper.thm8_unified_3x3_pillai_abc_skeletal_matrix_and_radical_floor_embedding' depends on axioms: [propext]
'RotatorCalculusPaper.thm9_universal_pillai_abc_differential_bezout_and_pade_laws' depends on axioms: [propext, Quot.sound]
'RotatorCalculusPaper.thm10_universal_root_free_cubic_pade_compression' depends on axioms: [propext, Quot.sound]
'RotatorCalculusPaper.thm11_universal_cross_floor_wronskian_and_p3_kernel' depends on axioms: [propext, Quot.sound]
'RotatorCalculusPaper.thm12_universal_reverse_pade_bezout_cubic_annihilation_and_radical_bound' depends on axioms: [propext, Quot.sound]
'RotatorCalculusPaper.thm13_universal_integer_mason_stothers_cubic_wronskian_and_fourth_power_det' depends on axioms: [propext, Quot.sound]
'RotatorCalculusPaper.thm14_master_pillai_and_abc_bilateral_convergence_chains' depends on axioms: [propext, Quot.sound]
'RotatorCalculusPaper.thm15_universal_cross_floor_k2_k3_sixth_power_genus10_lock' depends on axioms: [propext, Quot.sound]
'RotatorCalculusPaper.thm16_universal_weierstrass_stereographic_abc_embedding_into_z512_rotator' depends on axioms: [propext, Quot.sound]
```
(`0 sorryAx`, `0 Classical.choice`).
