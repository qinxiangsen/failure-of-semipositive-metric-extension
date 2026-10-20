# External inputs and formalization scope

For *Failure of semipositive metric extension in a smooth projective family*.
This inventory is based on the archived Lean sources and their existing acceptance records, not on the verification summary alone. It describes the trust boundary; it is not a new proof of the imported mathematics. The source-manuscript correspondence and current build results are separate documents.

## 1. Four different layers

1. **Lean's logical foundations:** `propext`, `Classical.choice`, and `Quot.sound`. These are not the analytic or geometric results listed below. A particular theorem may use only a subset.
2. **Explicit mathematical axioms:** twelve distinct declarations below. They are admitted universal inputs, not proved theorems of this project. Some are composite corollaries that include stated language translations, not verbatim single numbered theorems in a reference.
3. **External semantic identifications:** the twelve bridges in §3. These interpret proved coordinate/analytic certificates in the paper's usual geometric language. They are additional trusted mathematics even where no Lean `axiom` declaration is present. An axiom report cannot detect prose-level interpretation obligations.
4. **Paper-specific deductions:** instantiated equations, sections, transition functions, applicability hypotheses, numerical coefficients and obstruction arguments proved by the supplied Lean code, relative to the relevant inputs. The paper/source map identifies their exact scope and source correspondence status.

“No `sorry`” does not mean “no external mathematics,” and compilation does not establish that an encoded proposition is identical to the verified source manuscript's sentence.

## 2. Explicit mathematical inputs

The prefix of all declarations below is `FailureOfSemipositiveMetricExtension.Literature`. Their historical prefix was `MetricExtension.Literature`; renaming changes neither mathematical type nor proof status. Paths below are relative to the repository root. E01 is the original stage-9 snapshot; E13 is the independent-current snapshot. Copies in other snapshots are retained independently and need not be replaced by these representatives.

### A01: `cao_extension_via_projective_immersion_psh_translation`

- Exact declaration: `FailureOfSemipositiveMetricExtension.Literature.cao_extension_via_projective_immersion_psh_translation`.
- Representative source: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/CaoProjectivePsh.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/CaoProjectivePsh.lean).
- Interface/type locator: `FailureOfSemipositiveMetricExtension.CaoExtensionInterface.ExtensionStatement` (slash-separated names denote the component definitions, not a single declaration).
- Mathematical content and hypotheses: Projective-immersion/PSH version of Cao L2 extension; genuine proper family, actual line bundle, finite restriction and integrable adjoint input are supplied by caller.
- Used for: MAIN, EXTEND, NONEXT; these are legacy claim IDs, resolved to source-manuscript labels in the paper/source map.
- Reference recorded in the source review: Cao, [arXiv:1404.6937v2](https://arxiv.org/pdf/1404.6937v2), Theorem 1.1, together with the metric, Kähler and multiplier-ideal translations in Demailly’s [*Analytic Methods in Algebraic Geometry*](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf).
- Historical source SHA-256 before renaming: `ac994d1172b29c9d2f1f795d8f387626968ffae4617f43e71b2db1d13989cfdb`.

### A02: `log_sum_squares_plurisubharmonic`

- Exact declaration: `FailureOfSemipositiveMetricExtension.Literature.log_sum_squares_plurisubharmonic`.
- Representative source: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/FubiniStudy.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/FubiniStudy.lean).
- Interface/type locator: `FailureOfSemipositiveMetricExtension.PlurisubharmonicOn / logSumSquaresWeight` (slash-separated names denote the component definitions, not a single declaration).
- Mathematical content and hypotheses: Logarithm of a holomorphic squared-modulus sum is psh, including its common zero set.
- Used for: METRIC, MINIMAL, SIU; these are legacy claim IDs, resolved to source-manuscript labels in the paper/source map.
- Reference recorded in the source review: Demailly, [*Analytic Methods in Algebraic Geometry*](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf), Definition 1.4, properties 1.5, Example 1.9 and Example 3.14.
- Historical source SHA-256 before renaming: `19a0cc0def9c84f4e779431a09de9591f7f7628a5f9ab17627bd6824d3f3b8c8`.

### A03: `smooth_divisor_multiplier_germ`

- Exact declaration: `FailureOfSemipositiveMetricExtension.Literature.smooth_divisor_multiplier_germ`.
- Representative source: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/MultiplierSmoothDivisor.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/MultiplierSmoothDivisor.lean).
- Interface/type locator: `FailureOfSemipositiveMetricExtension.Multiplier.IntegrableGerm / Multiplier.SimpleEquationAt` (slash-separated names denote the component definitions, not a single declaration).
- Mathematical content and hypotheses: Single smooth-divisor multiplier ideal formula in genuine holomorphic stalks with actual weighted integrals; caller proves the simple-equation hypothesis.
- Used for: IDEAL, SECTION, FIRST4; these are legacy claim IDs, resolved to source-manuscript labels in the paper/source map.
- Reference recorded in the source review: Demailly, [*Analytic Methods in Algebraic Geometry*](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf), Definition 5.1 and Remark 5.9.
- Historical source SHA-256 before renaming: `6aa941cd395653951d32dec3607e298ac1a72437f60a9bc4ec0a3c0ab5312d28`.

### A04: `negative_curve_psh_removal_via_zariski_siu_translation`

- Exact declaration: `FailureOfSemipositiveMetricExtension.Literature.negative_curve_psh_removal_via_zariski_siu_translation`.
- Representative source: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/NegativeCurvePshRemoval.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/NegativeCurvePshRemoval.lean).
- Interface/type locator: `FailureOfSemipositiveMetricExtension.NegativeCurveRemovalInterface.RemovalStatement` (slash-separated names denote the component definitions, not a single declaration).
- Mathematical content and hypotheses: Generic surface Zariski/Siu removal plus explicitly trusted Chern/intersection/degree and psh representative translations. Caller supplies the negative curve, generators, tensor cocycle and exact degrees.
- Used for: MINIMAL, ZARISKI_GEOM, SIU; these are legacy claim IDs, resolved to source-manuscript labels in the paper/source map.
- Reference recorded in the source review: Boucksom, [*Divisorial Zariski decompositions on compact complex manifolds* (2004)](https://www.numdam.org/article/ASENS_2004_4_37_1_45_0.pdf), Theorems 4.5 and 4.8, §3.1 and §2.2.1; the additional general translations are disclosed in the source.
- Historical source SHA-256 before renaming: `91c734b402a66acb10f1d56735eb4a50cba60e620b462d864bba80d872da5027`.

### A05: `psh_curvature_current_lelong_via_distribution_translation`

- Exact declaration: `FailureOfSemipositiveMetricExtension.Literature.psh_curvature_current_lelong_via_distribution_translation`.
- Representative source: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/PshCurvatureLelong.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/PshCurvatureLelong.lean).
- Interface/type locator: `FailureOfSemipositiveMetricExtension.PshCurvatureCurrentInterface.PshCurrentStatement` (slash-separated names denote the component definitions, not a single declaration).
- Mathematical content and hypotheses: Local psh finite-a.e./L1 representative, distributional curvature, positivity/closedness, trace measure and Lelong mass/growth comparison. No paper-specific metric or value 1/2.
- Used for: METRIC, SIU; these are legacy claim IDs, resolved to source-manuscript labels in the paper/source map.
- Reference recorded in the source review: Demailly, [*Analytic Methods in Algebraic Geometry*](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf), properties 1.5, Theorem 1.7, §§1.12–1.16 and Theorem 2.8.
- Historical source SHA-256 before renaming: `82a7492b27479ae08dd38649530e22a15734e162422fcfc768cf39b60f561aa8`.

### A06: `cao_extension_proper_disc_kahler_psh_translation`

- Exact declaration: `FailureOfSemipositiveMetricExtension.Literature.cao_extension_proper_disc_kahler_psh_translation`.
- Representative source: [`snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/CaoGeneralKahler.lean`](../snapshots/E01/FailureOfSemipositiveMetricExtension/Literature/CaoGeneralKahler.lean).
- Interface/type locator: `FailureOfSemipositiveMetricExtension.GeneralCao.FiniteNormExtensionStatement` (slash-separated names denote the component definitions, not a single declaration).
- Mathematical content and hypotheses: Arbitrary-dimensional proper-disc Kähler Cao extension in the actual family/line/finite-norm interface; existence only, not optimal bound.
- Used for: CAO, ADJUNCTION; these are legacy claim IDs, resolved to source-manuscript labels in the paper/source map.
- Reference recorded in the source review: Cao, [arXiv:1404.6937v2](https://arxiv.org/pdf/1404.6937v2), Theorem 1.1, Remark 3 and Corollary 3.1.
- Historical source SHA-256 before renaming: `41d27cdac70305179e76a1af8aa71a9d4451137d5a7df1f4b22c163741592eec`.

### A07: `distributional_ddc_coordinate_gauge_covariance`

- Exact declaration: `FailureOfSemipositiveMetricExtension.Literature.distributional_ddc_coordinate_gauge_covariance`.
- Representative source: [`snapshots/E13/FailureOfSemipositiveMetricExtension/Literature/CurrentCovariance.lean`](../snapshots/E13/FailureOfSemipositiveMetricExtension/Literature/CurrentCovariance.lean).
- Interface/type locator: `FailureOfSemipositiveMetricExtension.CurrentCoordinateCovariance.CovarianceStatement` (slash-separated names denote the component definitions, not a single declaration).
- Mathematical content and hypotheses: Actual biholomorphic chart/gauge change gives distribution Hessian covariance including inverse-Jacobian density. Caller supplies integrability and exact weight transform.
- Used for: SIU; these are legacy claim IDs, resolved to source-manuscript labels in the paper/source map.
- Reference recorded in the source review: Demailly, [*Analytic Methods in Algebraic Geometry*](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf), §1.C, together with standard distributional coordinate calculus.
- Historical source SHA-256 before renaming: `0eaf2167747f6dcc832b5e433ba22828140e8ed4191850a6cc802062c477f348`.

### A08: `independent_current_psh_metric_reconstruction`

- Exact declaration: `FailureOfSemipositiveMetricExtension.Literature.independent_current_psh_metric_reconstruction`.
- Representative source: [`snapshots/E13/FailureOfSemipositiveMetricExtension/IndependentCurrentMetricBridge.lean`](../snapshots/E13/FailureOfSemipositiveMetricExtension/IndependentCurrentMetricBridge.lean).
- Interface/type locator: `FailureOfSemipositiveMetricExtension.IndependentCurrentMetricBridge.ReconstructionStatement` (slash-separated names denote the component definitions, not a single declaration).
- Mathematical content and hypotheses: On compact complex surface with genuine projective immersion, independent positive closed T in same real current deRham class as a finite-a.e. psh metric is represented by a compatible psh metric.
- Used for: SIU; these are legacy claim IDs, resolved to source-manuscript labels in the paper/source map.
- Reference recorded in the source review: Demailly, [*Analytic Methods in Algebraic Geometry*](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf), §6.A, formulas (6.1)–(6.2), together with the compact Kähler ddᶜ lemma and local plurisubharmonic regularization.
- Historical source SHA-256 before renaming: `91d05bbb043fa8ef607cc536a1fa3cd3e1bafa803a8cbc55b61e5dcaa80227b7`.

### A09: `smooth_rational_divisor_poincare_lelong_integration_translation`

- Exact declaration: `FailureOfSemipositiveMetricExtension.Literature.smooth_rational_divisor_poincare_lelong_integration_translation`.
- Representative source: [`snapshots/E13/FailureOfSemipositiveMetricExtension/Literature/PoincareLelongIntegration.lean`](../snapshots/E13/FailureOfSemipositiveMetricExtension/Literature/PoincareLelongIntegration.lean).
- Interface/type locator: `FailureOfSemipositiveMetricExtension.PoincareLelongIntegrationInterface.IntegrationStatement` (slash-separated names denote the component definitions, not a single declaration).
- Mathematical content and hypotheses: Actual parametrized smooth rational curve integration equals Poincaré–Lelong current for simple divisor equations, with explicit tangent-area density and normalization.
- Used for: SIU; these are legacy claim IDs, resolved to source-manuscript labels in the paper/source map.
- Reference recorded in the source review: Demailly, [*Analytic Methods in Algebraic Geometry*](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf), §1.C, formulas (1.15)–(1.20), together with the standard Poincaré–Lelong formula and the measure-zero omission of one parameter-chart point.
- Historical source SHA-256 before renaming: `408b24a77545544d03c5d04cf004c1293d9f19b6579b04d057159896f235e9b3`.

### A10: `residual_current_local_calculus`

- Exact declaration: `FailureOfSemipositiveMetricExtension.Literature.residual_current_local_calculus`.
- Representative source: [`snapshots/E13/FailureOfSemipositiveMetricExtension/CurrentResidualStandards.lean`](../snapshots/E13/FailureOfSemipositiveMetricExtension/CurrentResidualStandards.lean).
- Interface/type locator: `FailureOfSemipositiveMetricExtension.CurrentResidualStandards.ResidualCalculusStatement` (slash-separated names denote the component definitions, not a single declaration).
- Mathematical content and hypotheses: Generic local ddc linearity, positivity and global exactness for arbitrary positive scalar and supplied same global u; caller already proves all decompositions, finite/L1 conditions and current coefficient equalities. Does not invent u or the paper-specific 1/2 coefficient.
- Used for: SIU; these are legacy claim IDs, resolved to source-manuscript labels in the paper/source map.
- Reference recorded in the source review: Standard distributional differentiation and global ddᶜ-exactness; the composite interface is spelled out in `CurrentResidualStandards.lean`. For the current and potential conventions, see Demailly, [*Analytic Methods in Algebraic Geometry*](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf), §1.C and §6.A; this is not attributed to a single verbatim numbered theorem.
- Historical source SHA-256 before renaming: `c05ed61d9df06411cba234b7b24cc4deacf9c65eb71fa176fe50bfd8c4d57057`.

### A11: `reduced_curve_integration_lelong_one`

- Exact declaration: `FailureOfSemipositiveMetricExtension.Literature.reduced_curve_integration_lelong_one`.
- Representative source: [`snapshots/E13/FailureOfSemipositiveMetricExtension/CurrentResidualStandards.lean`](../snapshots/E13/FailureOfSemipositiveMetricExtension/CurrentResidualStandards.lean).
- Interface/type locator: `FailureOfSemipositiveMetricExtension.CurrentResidualStandards.DivisorNormalizationStatement` (slash-separated names denote the component definitions, not a single declaration).
- Mathematical content and hypotheses: Trace-mass Lelong normalization 1 for an actual smooth reduced curve integration current.
- Used for: SIU; these are legacy claim IDs, resolved to source-manuscript labels in the paper/source map.
- Reference recorded in the source review: Demailly, [*Analytic Methods in Algebraic Geometry*](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf), §2.B, formulas (2.7)–(2.10).
- Historical source SHA-256 before renaming: `c05ed61d9df06411cba234b7b24cc4deacf9c65eb71fa176fe50bfd8c4d57057`.

### A12: `positive_current_lelong_monotonicity`

- Exact declaration: `FailureOfSemipositiveMetricExtension.Literature.positive_current_lelong_monotonicity`.
- Representative source: [`snapshots/E13/FailureOfSemipositiveMetricExtension/CurrentResidualStandards.lean`](../snapshots/E13/FailureOfSemipositiveMetricExtension/CurrentResidualStandards.lean).
- Interface/type locator: `FailureOfSemipositiveMetricExtension.CurrentResidualStandards.LelongMonotonicityStatement` (slash-separated names denote the component definitions, not a single declaration).
- Mathematical content and hypotheses: Arbitrary positive T and I: caller first proves T-cI positive and I has Lelong number 1; infer existence and lower bound for T.
- Used for: SIU; these are legacy claim IDs, resolved to source-manuscript labels in the paper/source map.
- Reference recorded in the source review: Demailly, [*Analytic Methods in Algebraic Geometry*](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf), §2.B, formulas (2.7)–(2.10), together with positive-current mass monotonicity.
- Historical source SHA-256 before renaming: `c05ed61d9df06411cba234b7b24cc4deacf9c65eb71fa176fe50bfd8c4d57057`.

### Dependency closures are endpoint-specific

The historical Theorem A assembly endpoint uses A01–A05. The general-dimensional obstruction interface additionally uses A06. The E13 independent-current residual endpoint uses A02, A04, A05 and A07–A12 (nine mathematical axioms). Thus “twelve” is the union across the accepted material, not the closure of every declaration. E13 introduces six mathematical inputs beyond A01–A06; it must not be described as adding no axioms. The repository build reports must distinguish freshly executed `#print axioms` results from these historical closures.

The former sources contain stage-specific comments such as “proposed next-stage interface” or “separate from frozen stage 7.” They describe provenance, not a claim that the axiom was subsequently proved. In all snapshots the declarations listed here remain external inputs.

## 3. External semantic bridges (not newly reconstructed foundations)

The following are explicitly outside the implemented foundational development. A bridge ID is an inventory identifier, **not the name of a Lean theorem**. Exact Lean application endpoints are supplied below and in the correspondence table; there is intentionally no invented declaration for an unimplemented comparison functor.

### S01: Disc restriction and relative projectivity

Open-disc restriction of the same proper analytic submersion; Segre composed with the actual relative closed immersion.

Application snapshots: E07; legacy claim IDs: MAIN.

### S02: Projective fibre algebraization and rationality

Chow and algebraicity of the graph for compact projective fibres; actual dense-open blowdown biholomorphism gives birationality. No absolute GAGA on noncompact total space.

Application snapshots: E04,E06,E07; legacy claim IDs: MAIN,FAMILY.

### S03: Kähler inheritance

Pull back Fubini–Study forms and Euclidean base form along the proved jointly immersive map; no abstract existence premise substituted.

Application snapshots: E07,E13; legacy claim IDs: MAIN,CAO,SIU.

### S04: Line bundles, effective divisors and tensor/dual correspondence

Actual pullback/gain/simple-zero certificates identify O(H),O(E),L,K,A,ell,Q; O(D+E),dual,section product and ideal O(-D) are standard.

Application snapshots: E08,E09,E10; legacy claim IDs: BUNDLES,CENTRALCLASS,QCLASS,IDEAL,SMALL_NUM,EFFECTIVE.

### S05: Irreducible/reduced strict-transform interpretation

Projective line minus finitely many points is irreducible, its actual lifted closure is strict transform; explicit distinct witnesses and simple equations give reduced sum.

Application snapshots: E09,E10; legacy claim IDs: QCLASS,CENTRALCLASS.

### S06: Intersection, nefness and divisor class translations

Restriction degree equals intersection; normal degree equals selfintersection; globally generated implies nef; standard smooth point-blowup intersection/canonical formulas. Concrete H/E naming and specified blowup identity must be accepted.

Application snapshots: E01,E08,E14; legacy claim IDs: INTERSECTION,NEARNEF,ZARISKI_NUM,COEFFICIENT.

### S07: Assigned multiplicity polynomials and blowup sections

On the compact projective central fibre, standard GAGA for line bundles identifies holomorphic and algebraic H0; then standard blowup assigned-multiplicity polynomial correspondence applies to accepted concrete A and cubic coefficients/jets/span. No absolute GAGA on noncompact total space; stronger unaccepted all-holomorphic-sections classification is not used.

Application snapshots: E01,E08,E14; legacy claim IDs: CUBICSPAN.

### S08: Metric/current and real Chern interpretation

Compatible nondegenerate locally L1 psh weights are semipositive singular Hermitian metrics; Chern–Weil identifies same actual L curvature class with real c1(L). No integral Chern class or singular-cohomology comparison object is constructed.

Application snapshots: E01,E07,E13; legacy claim IDs: D01,D02,METRIC,SIU.

### S09: Lelong normalization and divisorial reading

Squared-norm weights and ddc=i/(2pi) partial partialbar; ddc log|w|²=[w=0]. Use standard coordinate invariance and generic-point reading of actual all-point trace-mass results.

Application snapshots: E07,E13; legacy claim IDs: D02,METRIC,SIU,COEFFICIENT.

### S10: Hisamoto4.12 standard interpretation

One-point incidence model=Bl_p(P2)=F1 after projective coordinate normalization; actual ruling fibre/product and bundle pullback proved. Standard degree/selfintersection and Fubini preserve usual metric L1 under projection. Not Example4.13.

Application snapshots: E11; legacy claim IDs: HIS01.

### S11: Blowup as graph closure and disjoint centre product

Standard Rees graph-closure theorem; disjoint centres allow simultaneous blowup of the product/intersection ideal. Concrete polynomial direction maps, exact comaximal product and actual graph closure are supplied by E14, not assumed.

Application snapshots: E05,E12,E14; legacy claim IDs: FAMILY,INTERSECTION,CUBICSPAN.

### S12: Algebraic/analytic closure and reduced structure comparison

Constructible complex graph has equal Euclidean/Zariski closure support; smooth coordinate-centre blowup is reduced; analytification and reduced closed analytic-subspace uniqueness upgrade same ambient support with actual holomorphic closed embedding. No arbitrary-base-change assertion or Homeomorph-only analytic inference.

Application snapshots: E14; legacy claim IDs: FAMILY.

### Concrete anchors for the interpretation layer

- Theorem A: `FailureOfSemipositiveMetricExtension.PaperTheoremA.actual_analytic_counterexample`, in `snapshots/E07/FailureOfSemipositiveMetricExtension/TheoremAAnalyticAssembly.lean`. Its analytic counterexample certificate is not a Lean implementation of all algebraic/analytic comparison theory.
- Blow-up identity: `FailureOfSemipositiveMetricExtension.CoordinateBlowupCandidate.RawAdapter.GraphClosure.actual_blowup_graph_certificate`, in `snapshots/E12_E14/FailureOfSemipositiveMetricExtension/CoordinateBlowupAdapter/ActualBlowupGraphCertificate.lean`. Its twelve fields prove the actual graph support, closed holomorphic embedding, injective tangent maps, polynomial direction formulas, disjoint centres, centre-ideal product/comaximality, and coordinate-centre identities. The final identification with the algebraic blow-up uses S11–S12 externally. A homeomorphism alone is not asserted to be biholomorphic; the reduced closed-analytic-subspace comparison is essential. The unused stronger route through reducedness of the raw four-equation quotient is not claimed as completed.
- Independent currents: `FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.FreshCurrentBridge.actual_independent_current_full_residual`, in `snapshots/E13/FailureOfSemipositiveMetricExtension/IndependentCurrentCompleteEndpoint.lean`. The input current is independent, not defined to be a chosen metric's curvature. `actualRealChernClass` in `IndependentCurrentMetricBridge.lean` is a real distribution-current class presented by reference curvature; its identification with the usual real first Chern class is S08. There is no construction of integral Chern classes or the comparison to singular cohomology.
- Hisamoto comparison: `FailureOfSemipositiveMetricExtension.Hisamoto.hisamoto_example_4_12_local_extension` in `snapshots/E11/FailureOfSemipositiveMetricExtension/HisamotoLocalExtensionEndpoint.lean` is the local product-neighbourhood result for Example 4.12 only. It does not prove that Example 4.13 admits local extension. Any current-paper discussion of Example 4.13 must be read as a checked literature argument, not coverage supplied by this endpoint.

## 4. References and exact extent of the source checks

These are the primary sources recorded by the prior source audits. This packaging pass reread the actual axiom/interface files and audit records; it did not independently reprove these theorems or claim a new full literature audit.

- J. Cao, [arXiv:1404.6937v2](https://arxiv.org/pdf/1404.6937v2), Theorem 1.1 (existence part), Remark 3 and Corollary 3.1. The source interfaces disclose the additional metric, Kähler and local-norm translations. No optimal constant is claimed.
- J.-P. Demailly, [*Analytic Methods in Algebraic Geometry*](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf): §§1–3, Definition 5.1/Remark 5.9 and §6.A as specified for each input. The archived source review used PDF SHA-256 `6f4682f322d6ae0c0ce3feae4964792c473a3d9051fe01288ef9017ca341d009`. Distributional coordinate change, regularization and exactness are composite standard consequences; do not read their Lean types as verbatim numbered statements in this book.
- S. Boucksom, [*Divisorial Zariski decompositions on compact complex manifolds*, Ann. Sci. ENS 37 (2004), 45–76](https://www.numdam.org/article/ASENS_2004_4_37_1_45_0.pdf): §2.2.1, §3.1 and Theorems 4.5/4.8. The surface case is used; no extra bigness assumption is silently added. Archived PDF SHA-256: `26db93abed6fefd98df2633428d2b5036725498a5d0bbb3a83a93cf96a4b495a`.
- Rees/graph and coordinate blow-up facts: Stacks Project tags [0804](https://stacks.math.columbia.edu/tag/0804), [02OS](https://stacks.math.columbia.edu/tag/02OS), [02NS](https://stacks.math.columbia.edu/tag/02NS), [080A](https://stacks.math.columbia.edu/tag/080A), [0808](https://stacks.math.columbia.edu/tag/0808), [0G8Q](https://stacks.math.columbia.edu/tag/0G8Q). No arbitrary-base-change/blow-up commutation theorem is assumed.
- Complex and Zariski closure of constructible sets: J. S. Milne, [*Algebraic Geometry*, Chapter 15, Proposition 15.2](https://www.jmilne.org/math/CourseNotes/AG15.pdf).
- Reduced analytic subspaces: Grauert–Remmert, [*Coherent Analytic Sheaves*](https://link.springer.com/book/10.1007/978-3-642-69582-7), analytic sets/reduced subspaces and ideal sheaves. The historical audit verified bibliographic and chapter information, not paywalled full text; no invented page theorem number is supplied. Demailly's [*Basic results on Sheaves and Analytic Sets*](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/sheaves.pdf), §4.E, analytic zero-set theorem 4.9, was an additional indexed source; the prior full-PDF fetch timed out.
- H. Hisamoto, [arXiv:1205.1953v2](https://arxiv.org/pdf/1205.1953v2), Examples 4.12–4.13. The local observation in the Lean source applies only to 4.12. These examples are not new mathematical axioms.

Chow, Segre, ordinary GAGA on the compact projective fibre, Picard/divisor/tensor interpretations and intersection theory remain the explicitly disclosed general foundations in S01–S12. They are not asserted to follow solely from the paper's bibliography, and no absolute GAGA on the noncompact total space is invoked.

## 5. What this pass actually checked

The twelve original source snapshots were inspected for the explicit axioms listed above and for proof placeholders. No executable-token occurrence of `sorry`, `admit`, or `sorryAx` was found in that source inspection. This lexical check is not compilation or an exhaustive semantic audit. The reviewer build summary separately describes actual compilation, external dependencies and same-run artifact reuse. Reviewers can reproduce compilation with the supplied scripts and inspect the resulting local output.

This supplement corresponds only to the verified source manuscript identified in the README and paper/source map.
