import FailureOfSemipositiveMetricExtension.CentralAdjointSection

/-! Exact local zero-set formulas for the genuine central sections, stated in
all eight actual two-dimensional charts without a residual bundle-frame assumption. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle
open scoped Manifold ContDiff

/-- Every prescribed fibre chart can be refined by a matching actual bundle frame. -/
theorem divisionPatch_refines_source (t : ℂ) (r : Fin 4) (e : Fin 2) (p : Fiber t)
    (hp : p ∈ FixedFiber.source t r e) : ∃ b, p ∈ divisionPatch t (r,e,b) := by
  classical
  let b := ((core t 0 (fun _ => 0)).indexAt p).2
  have hi := (mem_chartSource_iff r e (FixedFiber.inclusion t p)).mp hp
  refine ⟨b,hp,hi.1,?_⟩
  intro j
  by_cases hj : j = r
  · subst j
    simpa [divisionFrame,FailureOfSemipositiveMetricExtension.GlobalLineBundle.divisionFrame] using hi.2.1
  · have hm := ((core t 0 (fun _ => 0)).mem_baseSet_at p).2 j
    simpa [divisionFrame,FailureOfSemipositiveMetricExtension.GlobalLineBundle.divisionFrame,Function.update_of_ne hj,b] using hm

theorem WeightedDivisionData.quotientSection_zero_iff_local
    {a c : ℤ} {b d : Fin 4 → ℤ} (D : WeightedDivisionData a c b d)
    (j : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 j) :
    sectionValue D.quotientSection p = 0 ↔
      D.localCoefficient j.1 j.2.1 (FixedFiber.coordinates 0 j.1 j.2.1 p) = 0 := by
  rw [sectionValue_zero_iff D.quotientSection (divisionFrame j) p hp.2,
    D.quotientSection_coefficient j p hp]
  simp only [WeightedDivisionData.localQuotient,div_eq_zero_iff,
    D.otherDenominator_ne_zero j p hp,or_false]

theorem WeightedDivisionData.quotientSection_zero_iff_coordinates
    {a c : ℤ} {b d : Fin 4 → ℤ} (D : WeightedDivisionData a c b d)
    (r : Fin 4) (e : Fin 2) (p : Fiber 0) (hp : p ∈ FixedFiber.source 0 r e) :
    sectionValue D.quotientSection p = 0 ↔
      D.localCoefficient r e (FixedFiber.coordinates 0 r e p) = 0 := by
  obtain ⟨b,hb⟩ := divisionPatch_refines_source 0 r e p hp
  exact D.quotientSection_zero_iff_local (r,e,b) p hb

theorem WeightedDivisionData.quotientSection_zero_iff_param
    {a c : ℤ} {b d : Fin 4 → ℤ} (D : WeightedDivisionData a c b d)
    (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) (hq : q ∈ FixedFiber.domain 0 r e) :
    sectionValue D.quotientSection (FixedFiber.param 0 r e q) = 0 ↔ D.localCoefficient r e q = 0 := by
  have hp := (FixedFiber.chart 0 r e).map_target hq
  simpa only [FixedFiber.coordinates_param] using
    D.quotientSection_zero_iff_coordinates r e (FixedFiber.param 0 r e q) hp

/-- ℓ vanishes only in the X-charts at the first three centres, along slope zero. -/
theorem ellSection_zero_iff_param (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord)
    (hq : q ∈ FixedFiber.domain 0 r e) :
    sectionValue ellSection (FixedFiber.param 0 r e q) = 0 ↔ r ≠ 3 ∧ e = 0 ∧ q.2 = 0 := by
  rw [show sectionValue ellSection (FixedFiber.param 0 r e q) = 0 ↔ ellLocalCoefficient r e q = 0 from
    ellDivisionData.quotientSection_zero_iff_param r e q hq]
  by_cases hr : r = 3 <;> by_cases he : e = 0 <;> simp [ellLocalCoefficient,hr,he]

/-- Q has exactly the zeros of the explicit divided cubic in every actual chart. -/
theorem qSection_zero_iff_param (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord)
    (hq : q ∈ FixedFiber.domain 0 r e) :
    sectionValue qSection (FixedFiber.param 0 r e q) = 0 ↔ qLocalCoefficient r e q = 0 :=
  qDivisionData.quotientSection_zero_iff_param r e q hq

theorem ellSection_nonzero : ∃ p : Fiber 0, sectionValue ellSection p ≠ 0 :=
  ⟨auxiliaryWitness,ellSection_witness_ne_zero⟩

theorem qSection_nonzero : ∃ p : Fiber 0, sectionValue qSection p ≠ 0 :=
  ⟨auxiliaryWitness,qSection_witness_ne_zero⟩

theorem sigmaSection_zero_iff (p : Fiber 0) :
    sectionValue sigmaSection p = 0 ↔ sectionValue ellSection p = 0 ∨ sectionValue qSection p = 0 := by
  let i := (core 0 (-7) (fun _ => 3)).indexAt p
  change ((ellSection.coefficient i p * ellSection.coefficient i p) * qSection.coefficient i p) = 0 ↔
    ellSection.coefficient i p = 0 ∨ qSection.coefficient i p = 0
  simp only [mul_eq_zero,or_self]

/-- Zero sets of actual analytic fibre-bundle sections are closed, using their local frames. -/
theorem section_zeroSet_isClosed {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (s : SectionData t a b) :
    IsClosed {p : Fiber t | sectionValue s p = 0} := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  let i := (core t a b).indexAt p
  have hi : p ∈ baseSet t i := (core t a b).mem_baseSet_at p
  have hn : s.coefficient i p ≠ 0 := fun hz => hp ((sectionValue_zero_iff s i p hi).mpr hz)
  have hc := (s.analytic i).continuousOn.continuousAt ((baseSet_isOpen t i).mem_nhds hi)
  have hnb := hc.preimage_mem_nhds (isOpen_ne.mem_nhds hn)
  filter_upwards [(baseSet_isOpen t i).mem_nhds hi,hnb] with q hq hnq
  exact fun hz => hnq ((sectionValue_zero_iff s i q hq).mp hz)

theorem ellZeroSet_isClosed : IsClosed {p : Fiber 0 | sectionValue ellSection p = 0} :=
  section_zeroSet_isClosed ellSection

def ellLocalUnit (d : DivisionIndex) (p : Fiber 0) : ℂ :=
  (ellDivisionData.otherDenominator d p)⁻¹

theorem ellLocalUnit_ne_zero (d : DivisionIndex) (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    ellLocalUnit d p ≠ 0 := inv_ne_zero (ellDivisionData.otherDenominator_ne_zero d p hp)

theorem ellLocalUnit_contMDiffOn (d : DivisionIndex) :
    ContMDiffOn 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ) ω (ellLocalUnit d) (divisionPatch 0 d) := by
  have hinv : ContDiffOn ℂ ω (fun z : ℂ => z⁻¹) {z | z ≠ 0} :=
    contDiffOn_id.inv (fun _ h => h)
  exact hinv.contMDiffOn.comp (ellDivisionData.otherDenominator_contMDiffOn d)
    (fun p hp => ellDivisionData.otherDenominator_ne_zero d p hp)

/-- The exact simple local equation: slope times a nowhere-vanishing analytic unit. -/
theorem ellSection_coefficient_simple (d : DivisionIndex) (hr : d.1 ≠ 3) (he : d.2.1 = 0)
    (p : Fiber 0) (hp : p ∈ divisionPatch 0 d) :
    ellSection.coefficient (divisionFrame d) p =
      (FixedFiber.coordinates 0 d.1 d.2.1 p).2 * ellLocalUnit d p := by
  change ellDivisionData.quotientSection.coefficient _ _ = _
  rw [ellDivisionData.quotientSection_coefficient d p hp]
  simp only [WeightedDivisionData.localQuotient,ellDivisionData,ellLocalCoefficient,hr,
    he,ite_false,ite_true,div_eq_mul_inv,ellLocalUnit]

/-- Every zero of ℓ has one of these actual simple analytic local equations. -/
theorem ellSection_simple_at_zero (p : Fiber 0) (hz : sectionValue ellSection p = 0) :
    ∃ d : DivisionIndex, p ∈ divisionPatch 0 d ∧ d.1 ≠ 3 ∧ d.2.1 = 0 ∧
      ∀ q ∈ divisionPatch 0 d, ellSection.coefficient (divisionFrame d) q =
        (FixedFiber.coordinates 0 d.1 d.2.1 q).2 * ellLocalUnit d q := by
  obtain ⟨d,hp⟩ := divisionPatch_cover 0 p
  have he := ellDivisionData.quotientSection_zero_iff_local d p hp
  have hloc : ellLocalCoefficient d.1 d.2.1 (FixedFiber.coordinates 0 d.1 d.2.1 p) = 0 := he.mp hz
  have hr : d.1 ≠ 3 := by intro hr; simp [ellLocalCoefficient,hr] at hloc
  have hc : d.2.1 = 0 := by by_contra hc; simp [ellLocalCoefficient,hr,hc] at hloc
  exact ⟨d,hp,hr,hc,fun q hq => ellSection_coefficient_simple d hr hc q hq⟩

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
