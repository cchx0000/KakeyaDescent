# Analysis: "Filtered Descent for the Physical Kakeya Incidence" (Chenxi Cai, Sept 2026)

Analyst's note: the paper has **no** numbered Theorem/Lemma/Proposition environments.
All results are labeled items (**R5**, **R6**), numbered equations, and named displayed
estimates. The inventory below follows the paper's own numbering. Equation numbers are
quoted verbatim from the paper. Statements are paraphrased into precise plain language;
"δ^{-o(1)}" means: for every ε > 0, ≤ C(ε, d)·δ^{-ε} for δ small (a subpower loss).

## 0. What the paper does (one paragraph)

A finite weighted incidence system ("descent ledger") is built on a direction-separated
family of shaded δ-tubes: a symmetric joint packet law (17)/(21) carrying all support
marginals, insertion kernels (13), root exchange, and history trees in one probability
space. Two ledger rules drive everything: **R5** (one-point marginals of any retained
restriction of packet mass α are ≤ α^{-1}·µ_inc) and **R6** (the global confluence
L²/L¹ estimate (121), summing all histories in a load layer *before* estimating).
A Gram–Schmidt pivot stratification gives a broad vs. thickened-face dichotomy (42);
the history tree with least-common-ancestor charging reduces R6 to a single **root-cross
gate (142)**. The gate is closed analytically: d=2 by the hereditary planar Córdoba
estimate [2]; d=3 by the sticky Kakeya theorem + sticky/non-sticky reduction [7,10];
d=4 by directionwise sampling, an unbiased fibre lift, and the uniform marked 4D sticky
estimate [9]. For d ≥ 5 the marked root gate remains an input. The Selmer–Cartan tower
[1] is used only as passive structural provenance (it proves no estimate). A separate,
**unproved** hereditary *typed* statement would need a positive Hall/Radon–Nikodym
capacity (160) on correlated pair sources (§13.3 explicitly disclaims it).

---

## 1. Result inventory

### §1 — The finite physical descent ledger (standing rules)
- **Ledger properties 1–4 (§1, p.1–2).** The four concrete properties entering the
  scalar proof: (1) exact-support term = rooted transverse determinant, slot deletion =
  literal proper face; (2) insertion kernels compose by conditional probability
  (insertion order / confluence / restriction / rerooting compatible); **(3) = R5**;
  **(4) = R6**.
- **R5 — one-point marginal bound (§1.3, proved in (9), (25)).** *Assume* the symmetric
  packet law (17) (resp. its marked lift (22)) and condition on / restrict to an event
  (resp. hereditary mask) of retained packet mass α (resp. Pr(A)). *Then* every
  one-point (single-slot) marginal is dominated by α^{-1}·µ_inc (resp.
  Pr(A)^{-1}·µ_{Q,T₀}): precisely (9) Pr(Uᵢ ∈ B | A) ≤ µ_{Q,T₀}(B)/Pr(A), and (25)
  P̃^{w,A}((Q,Tⱼ,xⱼ) ∈ B) ≤ α^{-1}µ_inc(B). Before conditioning the constant is 1;
  retained mass α ≥ δ^{o(1)} gives loss ≤ δ^{-o(1)}.
- **R6 — global confluence estimate (§1.4, stated as (121) in §9.1).** *Assume* the
  history/load filtration. *Then* with N_{I,k}(x) = Σ_γ E_γ(ρ_γ 1_{Γ_k} f_{γ,I})(x)
  (all histories γ in one load layer summed **before** estimating),
  ∫N_{I,k}²/∫N_{I,k} ≲ δ^{-o(1)}·(L/(λ_I λ_{I\{0\}}))·B_{K_{I\{0\}}} uniformly in k.
  The paper proves R6 ⇔ (142) modulo the tree calculation (137)–(141).
- **(2)** (definition of the unmarked observable): E_inc(f) = Σ_γ ρ_γ E_γ(f_γ) with
  ρ_γ = d(π_γ)∗µ_γ/dµ_inc. Not replaceable by one normalized chart.
- **(1), (3), (7), (8)** — passive motivic decoration / common-controller comparison
  (structural provenance only; no analytic content).

### §2 — Fixed-root exact-support bridge
- **(4)** (definition): exact-support detector D_I(U) = det_W(s(U₁),…,s(U_r)).
- **(5)** (definition): physical packet cochain Z^{(d)}_{Q,T₀} = Σ_U µ_{Q,T₀}^{⊗r}(U)^{1/2} D_I(U) z_U.
- **(6) — ordered Cauchy–Binet norm identity.** ‖Z^{(d)}_{Q,T₀}‖² = Σ_U µ^{⊗r}_{Q,T₀}(U)|D_I(U)|²
  = r!·det M_{Q,T₀}, where M_{Q,T₀} = E_{U∼µ}[s(U)s(U)ᵀ]. (Proved; pure linear algebra.)
- **Literal side-face deletion (§2).** Deleting a side tube deletes exactly the tuple
  blocks containing it; the unnormalized detector energy can only decrease and stays
  equal to r!·det M for the restricted measure. Deleting i ∈ I° replaces the top wedge
  by its literal face.
- **(9)** — proved here (see R5 above).
- **(10) — fibre density / Fubini.** g_U(z) = ∫_{π_{T₀}^{-1}(z)} 1_{Y(U)}(x)dH¹(x),
  ∫_W g_U(z)dz = |Y(U)|. Projected mass is exact.
- **(11) — determinant projection identity.** det(e_{T₀},e_{U₁},…,e_{U_r}) =
  det_W(P_W e_{U₁},…,P_W e_{U_r}).

### §3 — Insertion spans and confluence at one root
- **(12)–(13)** (definitions): insertion-history span H_{A,B} and conditional kernel
  K_{A,B}(x_B|x_A) = P_B(x_B)/(P_A(x_A)·1_{x_B|_A=x_A}).
- **(14) — kernel chain rule.** K_{A,C}(x_C|x_A) = K_{B,C}(x_C|x_C|_B)·K_{A,B}(x_C|_B|x_A)
  for A ⊆ B ⊆ C (conditional-probability chain rule).
- **(15) — insertion confluence.** Both insertion orders agree:
  K_{A∪{i},A∪{i,j}}K_{A,A∪{i}} = K_{A∪{j},A∪{i,j}}K_{A,A∪{j}} = K_{A,A∪{i,j}}.
- **(16)** pull–push operator L_{A,B}; consequence L_{B,C}L_{A,B} = L_{A,C} (matrix
  composition).
- Raw lift count q_{A,B} retained by the span (used only as provenance, never as an
  analytic bound).

### §4 — The root-face span
- **(17)** (definition): symmetric packet law
  P_w(Q,T₀,…,T_r) = (W_Q/W)·∏_{j=0}^r (w_{Q,T_j}/W_Q), invariant under all permutations
  of slots.
- **(18) — one-slot marginal.** Every slot of P_w has exactly the coarse
  shaded-incidence marginal w_{Q,T_j}/W.
- **(19) — root-exchange sign.** det(e_{T_j},e_{T₀},…,ê_{T_j},…,e_{T_r}) =
  (−1)^j det(e_{T₀},…,e_{T_r}); ρ_{0j} carries Z^{(d)}_{Q,T₀} to the T_j-rooted packet
  with no norm/source loss.
- **(20)** root-face factorization: T₀-rooted I-packet →(ρ_{0j}) T_j-rooted I-packet
  →(del₀) T_j-rooted (I\{0\})-packet; averaged over j ∈ I° with weight 1/r.
- **Root-face R5 loss.** Branch condition retaining event E of the symmetric tuple law
  has Radon–Nikodym loss ≤ P_w(E)^{-1}; retained mass δ^{o(1)} gives δ^{-o(1)} loss.

### §5 — Global incidence gluing and shaded restrictions
- **(21)** (definition): incidence law dµ_inc(Q,T,x) = W^{-1}·1_{Y_Q(T)}(x)dx and
  weighted multiplicity m_a.
- **(22)–(23)** marked lift P̃^w and its slot marginals = dµ_inc.
- **(24)** global functor Φ_rec = ⊕_Q Φ^Q_rec (weighted direct sum over cubes).
- **(25)** — proved here (see R5).
- **(26)** root projection glues by ordinary pushforward; Σ_Q∫g_{Q,U} = |Y(U)|.

### §6 — Structural provenance and passive decorations (all structural)
- **(27)–(28)** dg representation Ξ_I of the normalized cobar–Rees controller;
  proves the comparison (8). **(29)–(31)** passive audit / normalized physical
  augmentation ε_phys (vertical decoration defects create no physical multiplicity).

### §7 — Quantitative thickening of support latching
- **(32)–(33)** Gram–Schmidt pivots p_j; |D_I(U)| = ∏_{j=1}^r p_j.
- **(34)** broad stratum: |D_I| ≥ κ^r. **(35)** near-face: |s_j − s̃_j| < κ and
  |D_I(s)−D_I(s̃)| ≤ κ with the second determinant zero.
- **(36)** carrier width a_face = δ + κ.
- **(37)** packet carrier mark c_pkt(ω) = (j, normal cap, offset bin).
- **(38) — cube-narrow field (physical source theorem, not formal).** On the retained
  incidence set there is ν_Q depending only on Q with |ν_Q·e_T| ≲ κ for every
  retained (Q,T).
- **(39) — cube Gram Cauchy–Binet.** E_{T₀,…,T_{d−1}∼µ_Q}[det(e_{T₀},…,e_{T_{d−1}})²]
  = d!·det G_Q.
- **(40)–(41) — cube-first Gram split.** Either det G_Q > β_Gr gives a
  source-subpower broad packet event of conditional mass ≥ c_d·β_Gr, or det G_Q ≤
  β_Gr and Markov deletion of a ρ-fraction leaves |ν_Q·e_T| ≤ κ (this proves (38)).
- **(42) — analytic support dichotomy.** Broad exact support (|D_I| ≥ κ^r, use
  determinant/root projection) vs. thickened proper face (p_j < κ, descend to
  I\{j} in width δ+κ).
- Hereditarity of the pivot partition + R5 bookkeeping: at most δ^{-o(1)} total
  loss; finitely many latching steps.

### §8.1 — Binary hardening and the planar base
- **(43)–(47) — binary strong shading.** On a projected line cell, g_C ≲ (δ/σ)m,
  g_C ≳ λmδ^{d−1}; the super-level set A_C = {g_C ≥ cλmδ/σ} satisfies
  |A_C| ≳ λσδ^{d−2}, g_C ≳ λmδ/σ on A_C, ∫_{A_C} g_C ≳ λmδ^{d−1}.
- **(48) — fibre cutoff L² bound.** ∫n_C² ≲_d mδ^{d−1}L, L = 1+log(1/δ).
- **(49)–(50) — translation load weights.** a_C = m_Cδ/σ; 0 < a_C ≲ 1 and
  sup_θ Σ_{C∈C_θ} a_C ≲ 1 (direction separation).
- **(52) — planar geometric estimate.** ∫_W W_pr² ≲ (L_σ/λ)∫_W W_pr,
  W_pr = Σ_C a_C 1_{A_C}, L_σ = 1+log(σ/δ). *No Fourier estimate used.*
- **(53) — planar cutoff.** With K_pr = L_σ/(τλ), H_pr = {W_pr ≤ K_pr}:
  ∫_{H_pr} W_pr ≥ (1−O(τ))∫W_pr and ‖W_pr 1_{H_pr}‖_∞ ≤ K_pr = δ^{-o(1)}.
- **(54) — negative result (counterexample).** An unweighted projected multiplicity
  bound is **false**: explicit δ^{-1}×δ^{-1} tube family with W_pr ≃ 1 but
  Σ1_{A_C} ≃ δ^{-1} everywhere; subpower retention would force K ≳ δ^{-1+o(1)}.

### §8.2 — Fibre-aware 3D descent
- **(55)–(58)** fibre-aware descendant: n_C(z,t) = Σ_U 1_{|t−h_U(z)|≲ℓ},
  ρ_C = n_C/a_C, N₃ = Σ_C a_C ρ_C 1_{A_C}, cλW_pr(z) ≲ ∫N₃dt ≲ W_pr(z).
- **(59) — 3D fibre-aware target.** ∃ hereditary H₃ ⊆ π^{-1}(H_pr) with
  ∫_{H₃}N₃ ≥ s₃∫N₃, ‖N₃ 1_{H₃}‖_∞ ≤ K₃, s₃^{-1},K₃ = δ^{-o(1)}.
  Marginal part proved by (52)–(53); remaining part = affine-fibre confluence
  packing, closed in §10.8 via sticky inputs (177).
- **(60)** J(U₁,U₂,U₃) = |det(e_{U₁},e_{U₂},e_{U₃})|; broad/narrow split for triples.
- **(61)** narrow rescaling δ′ = δ/κ (narrow branch = scale iteration of (59)).

### §8.3 — Marked 3→4 handoff
- **(62)–(63)** projected datum W₃, N₄ with cλW₃(z) ≲ ∫N₄dt ≲ W₃(z).
- **(64)–(65) — sticky coalescing.** Directionwise independent sampling + 3D sticky
  theorem + sticky/non-sticky reduction [7,10] give retained shadings with
  ∫M^ret_ω ≥ s_p∫M_ω, ‖M^ret_ω‖_∞ ≤ K_p (s_p^{-1},K_p = δ^{-o(1)}); expectation gives
  the coalesced fractional subsource W^f₃ with 0 ≤ w_C ≤ a_C 1_{A_C},
  ∫W^f₃ ≥ s_p∫W₃, ‖W^f₃‖_∞ ≤ K_p.
- **(66)–(68)** marked fibre interface; sufficient target **(67)**: a subsource
  Ñ₄ with ∫Ñ₄ ≥ s_f∫N^{pr}₄, sup_{z,I} |I|^{-1}∫_I Ñ₄dt ≤ K_f = δ^{-o(1)}.
- **(69)–(70) — marked fibre collision energy target.** E_fib = ∫(N^{pr}₄)²;
  sufficient: E_fib ≤ A_fib∫N^{pr}₄, A_fib = δ^{-o(1)}.
- **(71)–(72)** size-biased Markov truncation gives the same interval bound with
  K_f = A_fib·τ^{-1}.
- **(73)–(74) — history recombination.** Prefix-tree calc gives
  Σ_{a(γ,γ′)≠r∗}∫v_γv_{γ′} ≲ δ^{-o(1)}B^{pred}_{fib}∫N^{pr}₄; the **remaining root term**
  (74) Σ_{a(γ,γ′)=r∗}∫v_γv_{γ′} ≲ δ^{-o(1)}B^{pred}_{fib}∫N^{pr}₄ is the 3→4
  specialization of (142).
- **(75)–(78) — fibre-carrier packing.** b^{fib}_r ≲ min{1, rI^{fib}_r/(λN_{fib})};
  non-saturated shells (Σ_r rI^{fib}_r/(λN_{fib}) = o(1)) deletable in-budget;
  saturation forces I^{fib}_r ≳ λN_{fib}/r.
- **(79)** J₄(U₁,…,U₄) = |det(e_{U₁},…,e_{U₄})|; broad part by multilinear Kakeya
  [3,12]; narrow part rescales by **(80)** δ′ = δ/κ (same marked-fibre problem).
- **(81) — terminal marked estimate (interface to [9]).**
  |U(V,Y;Q_fib)| ≥ δ^{o(1)}Σ_V|Y(V)|, µ(V,Y;Q_fib) ≤ δ^{-o(1)}. *Supplied by the
  uniform marked 4D sticky theorem [9]; not proved here.*
- **(82)–(83)** honesty bookkeeping: power loss η₄ stays a power loss; the
  filtration never converts δ^{η₄+o(1)} into δ^{o(1)} (the 13/4 estimate [8] is
  therefore unusable).
- **(84)–(86)** schematic recursion R₄(δ) ≲ δ^{-o(1)} + κ^{-C}R₄(δ/κ); a pure
  narrow chain forces power loss (85); a successful recursion would need (86)
  with G(κ_j) = δ^{-o(1)} — exactly the missing fibre-spreading estimate.

### §8.5–8.7 — Randomized lifting, low-occupancy branch, flag obstruction
- **(87)–(93)** unbiased lifted load Z_ω with E_ωZ_ω = N^{pr}₄ (89);
  **(90)–(91)** ∫Z_ω² ≲ (K_pL/(aλ²s_p))∫Z_ω hence E_fib ≲ (K_pL/(aλ²s_p))∫N^{pr}₄;
  **(92)**: shells with a^{-1} = δ^{-o(1)} close using only the 3D sticky theorem;
  remainder reduced to **(93)** a = δ^{β+o(1)} (fixed β > 0) with correlated affine
  fibre intervals.
- **(94)–(102)**: pointwise broad/narrow split; narrow part enters one coherent
  hyperplane carrier (97); obstruction between (97) and (100) = anisotropic gate
  **(102)**: |U(P,Y;F)| ≥ δ^{o(1)}Σ|Y(P)| uniformly in plank aspect ratios
  (a sharper form of the missing fibre-spreading estimate).
- **(103)–(109)** flag tensorization: sufficient condition (104); **(106)** finite
  model with r^{mode}_+ = κ^{mode}_+ = R (positive mode rank can be power-large
  while marginals are uniform — marginal estimates + positive coalescence cannot
  prove the general gate); scalar shadows (107)–(109).

### §8.8 — Stronger projection hypothesis (conditional, unavailable)
- **(110)–(116)**: *If* unweighted shadings B_C with (110) existed, the factorized
  fibre calculation would give the rootwise cutoff (115) B_d ≲ B_{d−1}δ^{-ζ}L/(λλ_{d−1}).
  By (54) this hypothesis is false in general; **not used** as an unconditional route.

### §9.1 — Global first-failure decomposition
- **(117)** (definition): hereditary cutoff B_X = inf{B : ∃ hereditary E_X,
  ∫_{E_X^c} m_X ≤ τ(δ)∫m_X, m_X 1_{E_X} ≤ B a.e.}.
- **(118)** Reedy triangle L^{phys}_I → K^{phys}_I → C^{phys}_I (structural).
- **(119)** support strata partition: 0 ≤ h_J ≤ 1, Σ_{J⊆I} h_J = 1 (no duplication).
- **(120)–(121) = R6** (see §1).
- **(122) — support-step recurrence.** B_{K_I} ≲ B_{L_I} + δ^{-o(1)}·(L/(λ_Iλ_{I\{0\}}))·B_{K_{I\{0\}}}.

### §9.2 — Support recurrence and source-mass ledger
- **(123)** latching recombination: B_{L_I} ≲_d δ^{-o(1)} max_{J⊊I} B_{K_J}.
- **(124) — closed support recurrence.**
  B_{K_I} ≲_d δ^{-o(1)}·max_{J⊊I}B_{K_J} + (L/(λ_Iλ_{I\{0\}}))·B_{K_{I\{0\}}}.
- **(125)** iteration: B_{K_I} ≲_d δ^{-o(1)}·B_{K_2} (if λ_J ≥ δ^{o(1)}).
- **(126)–(128) — source-mass ledger.** Branch count P_δ ≤ C_d L^{C_d}β_{Gr}^{-C_d}κ^{-C_d} = δ^{-o(1)};
  Σ∫N_{I,k} ≲_d P_δ^{C_d}I_{cur}; retained packet mass α ≳_d δ^{o(1)},
  λ_J^{-1} ≲_d λ_{in}^{-1}P_δ^{C_d} = δ^{-o(1)}.

### §9.3 — Terminal unweighting
- **(129)–(130).** Averaged slot density h (129) with ∫h dµ_inc = α gives a set E,
  µ_inc(E) ≥ α/2, with **(130)** m_E ≤ (4/α²)·B_{K_I}: a genuine ordinary-incidence
  descendant with only δ^{-o(1)} loss once R6 holds and α = δ^{o(1)}.

### §10.1 — History tree and LCA charge
- **(131)–(136)** tree setup: u_γ ≥ 0, ∫N²_{I,k} = Σ_{γ,γ′}∫u_γu_{γ′}; W_a = Σ_{γ∈Desc(a)}u_γ;
  children partition descendants (133); internal node = observable at a strict
  predecessor (134); induction invariant W_a ≤ B^{pred}_I for proper a; well-founded
  order (135) (|I|, ℓ(χ), n); minimal leaf (2,0,0) = planar Córdoba base.
- **(137)–(139) — LCA charge.** c_{γ,γ′} = u_γu_{γ′}/W_{a(γ,γ′)};
  u_γu_{γ′} ≤ B^{pred}_I·c_{γ,γ′}; Σ_{a(γ,γ′)≠r∗}c_{γ,γ′} ≤ H_{I,k}N_{I,k},
  H_{I,k} = δ^{-o(1)} (refined tree height).
- **(140)–(141) — unconditional tree output.**
  ∫N²_{I,k} ≲ δ^{-o(1)}B^{pred}_I∫N_{I,k} + X^{root}_{I,k}.
- **(142) — THE ROOT-CROSS GATE (headline).**
  X^{root}_{I,k} ≲ δ^{-o(1)}·B^{pred}_I·∫N_{I,k}.

### §10.2 — Fixed-carrier decomposition of the root term
- **(143)–(147)** X^{root} = X^{geom} + X^{dup} (144); exact positive identities
  (146)–(147) via terminal-tube loads D_{b,T}, D_T (145).
- **(148) — same-terminal-tube hardening (sufficient).** D_T(x) ≲ δ^{-o(1)}B^{pred}_I
  for every retained (x,T) implies the dup bound.
- **(149)** D_T ≤ F_T·B^{pred}_I; F_T(x) ≤ δ^{-o(1)} suffices.

### §10.3 — Common-source aggregation
- **(150)–(151) — aggregate comparison.** Disjoint cylinder restrictions give
  d(Σ_{ϑ(b)=θ,ȷ(b)=j}(Π_j)∗1_{C_{b,c}}P̃^{w,A})/dµ_inc ≤ α^{-1} = δ^{-o(1)}.
- **(152) — carrier count.** |C_κ| ≤ C_dκ^{-C_d} = δ^{-o(1)}.
- **(153) — duplicate closure.** D_T(x) ≤ Σ_{θ,j,c}W^{θ,j,c} ≲ |C_κ|B^{pred}_I
  ≲ δ^{-o(1)}B^{pred}_I. Closes X^{dup} on broad and narrow histories.
- One-point R5-insufficiency model (p.30): R leaf histories, u_γ = 1, same terminal
  tube → N = R, X^{root} = R²−R — shows chartwise R5 does not imply the dup bound;
  not an obstruction to (150).
- **(155) — sufficient concrete form of the root gate.**
  X^{geom} ≲ δ^{-o(1)}B^{pred}_I∫N, X^{dup} ≲ δ^{-o(1)}B^{pred}_I∫N.

### §10.4–10.5 — Positive routing; Hall capacity
- **(156)–(158) — exact typed target.** Λ^{rout}_ξ ≤ δ^{-o(1)}·Λ^{pred}_ξ for every
  strict ξ (158); kernels R_ξ land in strict predecessors, preserve the common
  lifted point.
- **(159)** unary destination ledger Σ_ξ∫N_ξ ≲_d δ^{-o(1)}∫N_{I,k}.
- **(160) — measurable Hall inequalities (equivalent to (158), C_δ = δ^{-o(1)}).**
  Λ^{root}_{I,k}(E) ≤ C_δΣ_ξΛ^{pred}_ξ(A_ξ(E)) ∀ measurable E. Proved equivalent via
  fibrewise max-flow/min-cut (finite alphabets).
- **(161)** weighted fibre bound (deterministic sufficient form).
- Diagonal confluence example (p.33): unary RN constants = 1 but diagonal cut
  forces C_δ ≥ R — tensoring two unary R5's cannot control correlated confluence.

### §10.6–10.9 — Cycle-space reduction; packing; maximal/set inputs
- **(162)–(166)**: forest charging; **(165)** C^{br}_{I,k} ≤ δ^{-o(1)}B^{pred}_I∫N_{I,k}
  (weighted cycle budget, sufficient for the scalar gate); (166) β₁ bound (coarser).
- **(167)** bush computation: ∫m² ≃ δ^{-(d−2)} (d ≥ 3) — pairwise geometry cannot
  prove (165) on the unpruned source.
- **(168)** the missing uniform pruning mask (one H for all cores; not proved
  in general).
- **(169)–(176)** average tube–core Carleson charge; (175) non-saturated shells
  already satisfy (169); saturation (176) = sticky alternative.
- **(177) — sticky Kakeya input [7,10].**
  |U(T,Y)| ≥ δ^{o(1)}Σ_T|Y(T)|, µ(T,Y) ≤ δ^{-o(1)}. *Imported, not proved.*
- **(178)** Kakeya maximal conjecture (hereditary form) — **conjectural**;
  implies the hereditary scalar root gate (181) but is NOT used (stronger than needed).
- **(182)–(184)** Wang–Zahl set theorem [6] via [10]: (182)
  |U(T,Y)| ≥ S_δ|T||T|, S_δ = δ^{o(1)}; the mask H_{WZ} (183)–(184) gives the
  scalar 3D gate. *Imported.*
- **(185) — refinement statement** (equivalent to the shaded Kakeya set estimate
  up to subpower factors): the exact strength needed; strictly weaker than (178).
- **(186)** pointwise broadness transfer — **false in general** (disjoint-shading
  counterexample); another form of the packing problem.

### §10.10–10.17 — Forest congestion, typed routing, LP (mostly the unproved typed route)
- **(187)–(191)** weighted fundamental-cycle congestion κ_{F°}, exact cut formula
  (188)–(189); (191) ess sup κ_{cyc} ≤ δ^{-o(1)} ⟹ (165) (scalar graph criterion).
- **(192)–(193)** motivic-admissible forests; κ_{mot} (structural refinement).
- **(194)** typed chord-routing estimate ⟹ (165).
- **(196)** hybrid Hall capacity ⟹ (165).
- **(197)–(200)** faithful positive cycle realization (structural; K-theory
  contribution, no estimate).
- **(201) — external-product pair estimate** (proved from Fubini + unary R5).
- **(202)–(203)** mode number = chromatic number of conflict graph; χ ≤ 2+β₁.
- **(204)–(205)** fractional mode capacity κ^{mode}_+ and its LP dual.
- **(206)–(207)** finite LP formulation of the typed realization + Farkas dual
  (exact feasibility test).
- **(208)–(209)** divided-power identity; P^{root}_{I,k} = Σ_{b<b′}W_bW_{b′} ≥ 0,
  X^{root} = 2∫P^{root} (algebraic controller; no positivity of kernels).
- **(210)–(212)** pair base change K^{[2]}; algebraic candidate R_{alg}(γ,γ′)
  (may have signs — the missing refinement is exactly (160)/(161)).

### §11–13 — Base, termination, closure
- **§11**: hereditary planar Córdoba [2] (imported) gives the |I|=2 base
  B_{K₂} ≲ δ^{-o(1)} (when λ₂ ≥ δ^{o(1)}); induction on |I| via (124).
- **(213)** complexity c(η;I,χ,ν,n;N_s) strictly decreases along every branch
  (finite descent; structural, no analytic gain).
- **§13.2 — scalar analytic closure** (the theorem; see §2 below).
- **§13.3 — the separate typed requirement** (explicitly unproved: needs (160)/(207)).
- **(214) — terminal incidence count.** ∪_T Y′(T) ≳_d δ^{o(1)}·I_in; for N_T tubes
  with |Y(T)| ≥ λ_inδ^{d−1}: ∪Y′(T) ≳ δ^{o(1)}·N_Tλ_inδ^{d−1}.

---

## 2. Headline result

The single main theorem is the **scalar filtered-descent closure** (§13.2), whose
analytic core is the **root-cross gate (142)**. Stated precisely:

**Theorem (filtered estimate; scalar closure through d = 4).**
Fix a finite direction-separated family of shaded δ-tubes with hereditary shading
density λ_in^{-1} = δ^{-o(1)} (otherwise keep λ-factors explicit), and finite support,
coefficient, confluence, and Cartan ceilings. Let B_{K_I} be the hereditary cutoff
(117) at support I. Then:

1. (Analytic gate, (142).) At every retained support I and load shell k, the
   root-born pair collision mass satisfies
   X^{root}_{I,k} ≲ δ^{-o(1)} · B^{pred}_I · ∫ N_{I,k},
   where X^{root}_{I,k} = Σ_{a(γ,γ′)=r∗}∫u_γu_{γ′} sums only history pairs whose
   least common ancestor is the tree root, and
   B^{pred}_I = δ^{-o(1)}·(L/(λ_Iλ_{I\{0\}}))·B_{K_{I\{0\}}}.
   This is supplied: in d = 2 by the hereditary planar Córdoba estimate [2];
   in d = 3 by (52)–(59) plus the sticky Kakeya theorem and sticky/non-sticky
   reduction [7,10] (via (177)); in d = 4 by directionwise sampling, the unbiased
   fibre lift (88)–(92), and the uniform marked 4D sticky estimate [9] (via (81)).

2. (Descent.) The history-tree calculation (137)–(141) reduces R6 to (142), so
   (121) holds; the support recurrence closes as (124), hence
   B_{K_I} ≲_d δ^{-o(1)}·B_{K_2} (125).

3. (Terminal count, (214).) There is an ordinary-incidence descendant with
   ⋃_T Y′(T) ≳_d δ^{o(1)}·Σ_T|Y(T)|; in particular for N_T tubes with
   |Y(T)| ≥ λ_inδ^{d−1}, ⋃Y′(T) ≳ δ^{o(1)}·N_Tλ_inδ^{d−1}.

For d ≥ 5 the analogous source-hereditary marked root gate is **not** proved and
remains an explicit input. The hereditary *typed* statement (Hall capacity (160))
is explicitly **not** claimed (§13.3).

---

## 3. Dependency graph

```
EXTERNAL INPUTS (imported, not proved)
 [2] Córdoba planar ──► base B_{K₂} (§11); also (52)–(59) marginal part
 [7,10] sticky 3D + sticky/non-sticky ──► (64)–(65) coalescing ──► (59)/(177)
 [9] marked 4D sticky ──► (81) ──► root gate in d=4
 [3,12] multilinear Kakeya ──► broad parts (60), (79), §8.6
 [6] Wang–Zahl 3D set ──► (182)–(184) (alternative 3D scalar closure)
 [1] Selmer–Cartan tower ──► structural provenance ONLY: (1),(3),(7),(8),
      (27)–(31),(118),(192),(197)–(200),(212). No estimate flows from [1].
 [178] Kakeya maximal conjecture ──► (181) [NOT used; stronger than needed]

FINITE LEDGER (proved in-paper, elementary)
 (9)/(25) R5 ◄── conditional probability + symmetry of (17)/(22)
 (14)(15)(16) insertion/confluence ◄── chain rule for conditional probability
 (17)(18)(19)(20) symmetric law, marginals, root exchange ◄── definitions
 (6) Cauchy–Binet norm ◄── linear algebra
 (10)(11) fibre density, det projection ◄── Fubini, linear algebra
 (32)–(42) pivot stratification & dichotomy ◄── Gram–Schmidt, (39), Markov (41)
 (52)(53) planar estimate ◄── elementary tube geometry (48)–(50); NO Fourier
 (54) counterexample ◄── explicit construction (blocks the unweighted route)
 (90)(91) randomized lift energy ◄── Cauchy–Schwarz, (48), Jensen
 (106) mode-rank obstruction ◄── finite matching / LP duality
 (119) strata partition ◄── disjointness
 (126)–(128) source-mass ledger ◄── counting (branch types × cardinalities)
 (130) terminal unweighting ◄── (121) + Markov on slot density (129)
 (131)–(141) tree LCA charge ◄── finite tree combinatorics + predecessor induction
 (143)–(147) root-term identities ◄── positivity + disjointness
 (150)–(153) duplicate closure ◄── (25) [R5] + carrier count (152)
 (162)–(166) forest charging ◄── finite graph combinatorics
 (171)–(176) carrier packing ◄── tube geometry (volumes), no sticky input
 (183)–(185) set-input refinement ◄── (182) + Markov
 (187)–(191) weighted congestion duality ◄── finite Hall duality
 (201)–(207) external product, mode LP, Farkas ◄── Fubini, finite LP duality
 (208)(209) PD identity ◄── algebra
 (213) termination ◄── lexicographic well-founded order
 (214) terminal count ◄── incidence counting + (130)

THE SPINE (conditional chain)
 (142) root gate
   ├──► (121) R6        [via (141): tree calc is unconditional]
   ├──► (122)(124)(125) support recurrence [via (123) latching]
   ├──► (130) terminal descendant
   └──► (214) terminal count
 (142) itself ◄── d=2: [2]; d=3: [7,10] via (59)/(177); d=4: [9] via (81);
      dup part unconditionally via (148)–(153); geom part = the hard input.

THE UNPROVED TYPED BRANCH (explicitly disclaimed, §13.3)
 (158) ⟺ (160) Hall inequalities ⟺ (207) Farkas; sufficient: (161), (194),
 (196), (204). Structural inputs (192),(197)–(200),(212) name destinations
 but prove no capacity. NOT part of the scalar theorem.
```

---

## 4. Formalization tractability (Lean 4 + Mathlib)

General remarks. The paper's "δ^{-o(1)}" is an asymptotic bookkeeping device; a
faithful formal statement should use an explicit subpower formulation, e.g.
"∀ ε > 0, ∃ C(d,ε), ∀ δ < δ₀(ε): … ≤ C·δ^{-ε}" or carry an explicit slowly-varying
loss function. The finite tube families, direction sets, and history trees are
`Finset`-level combinatorics — well supported. Measure theory (µ_inc, Radon–Nikodym
densities, conditional kernels) would need `MeasureTheory` and is the main cost
driver; several milestones can be stated purely finitely (counting measures on
finite packet sets), avoiding general measure theory.

**(a) Elementary — provable now with reasonable effort.**
- R5 core (9): finite conditional probability, `Finset`/`PMF` manipulation.
- Insertion kernel chain rule (14), confluence (15), pull–push composition (16):
  finite sums, directly formalizable.
- Symmetric law marginals (18), root-exchange sign (19): elementary.
- R5 under restriction (25): the workhorse; finite version is elementary.
- Cauchy–Binet packet identity (6): needs the ordered Cauchy–Binet formula
  (check Mathlib's `Matrix` Binet–Cauchy coverage; else prove for the Gram case).
- Gram–Schmidt pivot identities (32)–(35), broad/narrow dichotomy (42): linear
  algebra + elementary estimates.
- History-tree LCA charge (131)–(141): finite rooted trees, the identities
  (133),(138),(139) and the induction invariant are clean combinatorics; the
  analytic induction hypothesis enters only as a black-box bound on proper nodes.
  **This is the best "deep but elementary" milestone.**
- Fixed-carrier identities (143)–(147), duplicate closure (148)–(153): finite
  sums + the R5 bound (150)–(151); the one-point insufficiency model is a nice
  standalone counterexample.
- Bush computation (167), carrier-packing shells (171)–(176), average charge
  (171): elementary volume counting.
- Mode-rank obstruction (106), external-product estimate (201), mode LP duality
  (204)–(205), Farkas feasibility (206)–(207): finite linear programming /
  combinatorics; Mathlib has Farkas-type lemmas (`LinearMap`/`Matrix` duality
  — coverage to be checked, but the finite-dimensional statements are standard).
- Divided-power identity (208)–(209): pure algebra.
- Termination measure (213): well-founded lexicographic order — routine.
- Terminal incidence count (214): counting, given (130).
- Counterexamples (54), (186-false): explicit finite constructions — good
  "negative" milestones.

**(b) Stateable faithfully; proofs need deep analysis (import as hypotheses).**
- Hereditary planar Córdoba estimate → (52)–(53) ⇒ base B_{K₂}: the *statement*
  (185) at d=2 is formalizable; the proof is Córdoba [2] — import as an axiom.
- Sticky coalescing (64)–(65): needs [7,10] as axioms (probabilistic method part
  is elementary given the 3D input).
- Marked 4D terminal estimate (81): needs [9] as an axiom (unpublished companion
  manuscript — flag this).
- The root gate (142) in d ≤ 4: stateable; its proof is exactly the imported
  hard analysis. The *conditional* theorem "sticky inputs + (142) ⇒ R6 ⇒ closed
  descent (124)(125)(214)" is the honest formalization target.
- (59), (70), (74), (155): all conditional on the above inputs.
- Wang–Zahl import (182)–(184): alternative 3D closure; import as axiom.
- The maximal-conjecture route (178)–(181): **do not formalize** (conjectural).

**(c) Structural/motivic bookkeeping — no analytic content; formalizing means
formalizing [1].**
- (1), (3), (7), (8), (27)–(31), (118), (156)–(161), (192)–(200), (210)–(212):
  the Selmer–Cartan comparison, dg representation, K-theoretic cycle
  realization. The paper itself stresses these prove no estimate. **Recommend
  excluding from any mission** except as documentation. Note the paper's own
  warning: the q² confluence line records provenance and "is never used as an
  analytic estimate."

Honesty note for mission design: the paper's genuine *proved* analytic content
is (i) the finite ledger (R5, insertion, root exchange), (ii) the pivot
stratification, (iii) the planar estimate (52)–(53) (elementary proof given),
(iv) the tree reduction of R6 to (142), (v) the duplicate closure (150)–(153),
(vi) the elementary packing/ledger counting. Everything else in the closure is
an *import interface* to [2],[7],[9],[10] (or the disclaimed typed route).
Milestones should reflect this: prove the ledger + reduction unconditionally,
and state the analytic closure as explicitly conditional on named imported
estimates.

---

## 5. Suggested milestones (for a Prove2me mission proposal)

Each milestone states what the Lean formal statement should assert. "Subpower"
below means the explicit ε-formulation: ∀ ε>0, ≤ C(d,ε)·δ^{-ε}.

**M1 — R5: one-point marginal bound ((9), (25)).**
Formalize the finite symmetric packet law: a finite set of tubes with weights,
the product/symmetric joint law on ordered r-tuples, and prove that every
one-point marginal equals the base law before conditioning, and that after
conditioning on (resp. restricting by a symmetric mask of) retained packet mass
α, every one-slot marginal is bounded by α^{-1} times the base incidence law.
This is the source ledger's most-used rule; its proof is elementary conditional
probability plus the symmetry of the joint law, and it should be proved
unconditionally in Lean.

**M2 — Ordered Cauchy–Binet packet norm identity ((6)).**
For the packet cochain Z = Σ_U p(U)^{1/2}det(s(U₁),…,s(U_r))z_U over ordered
r-tuples with one-point law µ, prove ‖Z‖² = Σ_U p(U)|det|² = r!·det M with
M = E_{U∼µ}[s(U)s(U)ᵀ]. Pure linear algebra (ordered Cauchy–Binet); check
Mathlib's Binet–Cauchy coverage first. Unconditional.

**M3 — Insertion kernels: chain rule and confluence ((13)–(16)).**
Given finite packet sets X_A with marginals P_A of a joint law P_I, define the
conditional insertion kernels K_{A,B} and prove the chain rule
K_{A,C} = K_{B,C}∘K_{A,B}, the two-order confluence identity (15), and
L_{B,C}L_{A,B} = L_{A,C} for the pull–push operators. Finite-sum probability;
unconditional.

**M4 — Gram–Schmidt pivot stratification and the broad/narrow dichotomy
((32)–(42)).**
For vectors s₁,…,s_r define the pivots p_j = dist(s_j, span(s₁,…,s_{j−1})) and
prove |det| = ∏p_j; formalize the first-failed-pivot partition (r+1 disjoint
events exhausting the packet law), the broad bound |D_I| ≥ κ^r, the near-face
approximation (35), and the cube-Gram split (39)–(41) yielding the coherent
cube-normal field (38) after Markov deletion. Linear algebra + elementary
measure/counting; unconditional.

**M5 — History-tree LCA charge and reduction of R6 to (142) ((131)–(141)).**
Formalize finite rooted prefix trees of histories with leaf loads u_γ ≥ 0,
node aggregates W_a, the children-partition identity (133), the LCA
coefficient bound (137)–(139) Σ_{a(γ,γ′)≠r∗}c_{γ,γ′} ≤ H·N with H subpower,
and deduce the unconditional decomposition ∫N² ≲ δ^{-o(1)}B^{pred}∫N + X^{root}
(141). The proper-node bound is taken as a hypothesis (induction invariant),
so the milestone is: *given* the invariant on proper vertices, the tree
calculation isolates exactly the root term. Unconditional combinatorics.

**M6 — Common-source duplicate closure ((143)–(155)).**
Decompose the root term by terminal tube, prove the exact positive identities
(146)–(147), and prove the duplicate bound X^{dup} ≲ δ^{-o(1)}B^{pred}∫N via
the disjoint-cylinder aggregate comparison (150)–(151) and the carrier count
(152)–(153). Include the one-point insufficiency model (R unit-mass leaves,
same terminal tube, X^{root} = R²−R) as a certified counterexample showing
chartwise R5 does not suffice. Unconditional.

**M7 — The root-cross gate (142), d ≤ 4, from named analytic inputs.**
The formal statement: under the hypotheses (H2) hereditary planar Córdoba
estimate [2], (H3) sticky Kakeya + sticky/non-sticky reduction [7,10],
(H4) uniform marked 4D sticky estimate [9] — each imported as an explicit
axiom with its exact quantitative form ((53), (177), (81)) — the root-cross
estimate X^{root}_{I,k} ≲ δ^{-o(1)}B^{pred}_I∫N_{I,k} holds at every retained
support/load stage in d = 2, 3, 4. The proof obligation inside the mission is
the *assembly*: (73)–(74) history recombination, (64)–(65) sticky coalescing,
the unbiased lift (88)–(92), and the reduction of the low-occupancy source to
(81). Flag that [9] is an unpublished companion manuscript.

**M8 — Closed descent: support recurrence and terminal count
((121)–(130), (214)).**
Assuming M7 (hence R6), prove the support-step recurrence (122), the latching
bound (123), the closed recurrence (124) and its iteration (125)
B_{K_I} ≲_d δ^{-o(1)}B_{K_2}, then the terminal unweighting (130) and the
incidence count (214): ⋃_T Y′(T) ≳_d δ^{o(1)}Σ_T|Y(T)|. The source-mass ledger
(126)–(128) (branch counting, retained mass α ≳ δ^{o(1)}) is proved
unconditionally as part of this milestone. This is the paper's scalar theorem
in formalizable form.

**M9 (optional, negative) — Unweighted projection is false ((54)).**
Formalize the explicit δ^{-1}×δ^{-1} tube family with weights a_C = δ satisfying
the translation bound (50) and W_pr ≃ 1 but Σ1_{A_C} ≃ δ^{-1} everywhere, proving
that no subpower unweighted multiplicity cutoff exists. Documents *why* the
fibre-aware formulation (59) is necessary. Unconditional, elementary.

Notes for the mission captain: M1–M6 + M9 are unconditional and elementary
(combinatorics, linear algebra, finite probability) — suitable as directly
provable missions. M7 is the analytic core and must list [2],[7],[9],[10] as
imported hypotheses with exact statements; M8 is conditional on M7. The entire
typed/Hall-capacity apparatus of §10.4–10.5, §10.10–10.17 ((158)–(161),
(192)–(207)) is explicitly disclaimed by the paper (§13.3) and should **not**
be proposed as missions. The d ≥ 5 root gate is an open input, not a milestone.
