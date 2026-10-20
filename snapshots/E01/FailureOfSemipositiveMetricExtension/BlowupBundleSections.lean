import FailureOfSemipositiveMetricExtension.BlowupLineBundle
import FailureOfSemipositiveMetricExtension.PencilSections

/-! Coherent polynomial local data are now actual continuous sections of the
glued complex line bundle, with a chart-independent vanishing criterion. -/
namespace FailureOfSemipositiveMetricExtension.BlowupLineBundle
noncomputable section
open FailureOfSemipositiveMetricExtension.Blowup FailureOfSemipositiveMetricExtension.BlowupSections Set Bundle
open scoped Topology
attribute [local instance] Classical.propDecidable

def coefficient {k : ℕ} (a : SectionData k) : Bool → Point → ℂ
  | false, p => a.x (coordinatesX p)
  | true, p => a.y (coordinatesY p)

theorem coefficient_transition {k : ℕ} (a : SectionData k) (i j : Bool) (p : Point)
    (hp : p ∈ baseSet i ∩ baseSet j) :
    gain k i j p * coefficient a i p = coefficient a j p := by
  cases i <;> cases j
  · simp [gain]
  · have hprod := slope_product p hp.1 hp.2
    have hs : (coordinatesX p).2 ≠ 0 := by
      intro hs; rw [hs,zero_mul] at hprod; exact zero_ne_one hprod
    have hc := a.compatible (coordinatesX p).1 (coordinatesX p).2 hs
    have ht : transition (coordinatesX p) = coordinatesY p := by
      rw [← coordinatesY_X (coordinatesX p) hs,X_coordinatesX p hp.1]
    rw [ht] at hc
    dsimp [gain,coefficient]
    have hpow : (coordinatesY p).2 ^ k * (coordinatesX p).2 ^ k = 1 := by
      rw [← mul_pow,mul_comm,hprod,one_pow]
    rw [hc,← mul_assoc,hpow,one_mul]
  · have hprod := slope_product p hp.2 hp.1
    have hs : (coordinatesX p).2 ≠ 0 := by
      intro hs; rw [hs,zero_mul] at hprod; exact zero_ne_one hprod
    have hc := a.compatible (coordinatesX p).1 (coordinatesX p).2 hs
    have ht : transition (coordinatesX p) = coordinatesY p := by
      rw [← coordinatesY_X (coordinatesX p) hs,X_coordinatesX p hp.2]
    rw [ht] at hc
    exact hc.symm
  · simp [gain]

theorem coefficient_continuousOn {k : ℕ} (a : SectionData k) (i : Bool) :
    ContinuousOn (coefficient a i) (baseSet i) := by
  cases i
  · exact a.x_holomorphic.continuous.comp_continuousOn homeomorphChartX.continuousOn
  · exact a.y_holomorphic.continuous.comp_continuousOn homeomorphChartY.continuousOn

/-- The actual bundle section determined by the coherent local coefficients. -/
def sectionValue {k : ℕ} (a : SectionData k) (p : Point) : (core k).Fiber p :=
  coefficient a ((core k).indexAt p) p

def sectionMap {k : ℕ} (a : SectionData k) : Point → (core k).TotalSpace :=
  fun p => ⟨p,sectionValue a p⟩

@[simp] theorem sectionMap_projects {k : ℕ} (a : SectionData k) (p : Point) :
    (core k).proj (sectionMap a p) = p := rfl

theorem sectionMap_localTriv {k : ℕ} (a : SectionData k) (i : Bool) (p : Point)
    (hp : p ∈ baseSet i) :
    (core k).localTriv i (sectionMap a p) = (p,coefficient a i p) := by
  rw [VectorBundleCore.localTriv_apply]
  congr 1
  exact coefficient_transition a ((core k).indexAt p) i p
    ⟨(core k).mem_baseSet_at p,hp⟩

/-- The gluing produces a genuine continuous section, not only transition data. -/
theorem sectionMap_continuous {k : ℕ} (a : SectionData k) : Continuous (sectionMap a) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  let i := (core k).indexAt p
  have hp : p ∈ baseSet i := (core k).mem_baseSet_at p
  have hnb : baseSet i ∈ 𝓝 p := (core k).isOpen_baseSet i |>.mem_nhds hp
  apply (((core k).localTriv i).toPartialHomeomorph.continuousAt_iff_continuousAt_comp_left
    (show sectionMap a ⁻¹' ((core k).localTriv i).source ∈ 𝓝 p from hnb)).mpr
  exact continuousAt_id.prodMk
    (((coefficient_continuousOn a i).congr (fun q hq =>
      congrArg Prod.snd (sectionMap_localTriv a i q hq))).continuousAt hnb)

/-- Invariant zero of the local data agrees with the zero vector in the actual fibre. -/
theorem sectionValue_zero_iff {k : ℕ} (a : SectionData k) (p : Point) :
    sectionValue a p = 0 ↔ a.zeroAt p := by
  dsimp [sectionValue,core]
  split_ifs with hx
  · change a.x (coordinatesX p) = 0 ↔ a.zeroAt p
    rw [← X_coordinatesX p hx,zeroAt_X_iff,coordinatesX_X]
  · have hy : p ∈ chartYSet := by
      have hp : p ∈ chartXSet ∪ chartYSet := by rw [chart_sets_cover]; trivial
      exact hp.resolve_left hx
    change a.y (coordinatesY p) = 0 ↔ a.zeroAt p
    rw [← Y_coordinatesY p hy,zeroAt_Y_iff,coordinatesY_Y]

/-- Central cubic systems generate a nonzero fibre vector at every exceptional point. -/
theorem central_actual_sections_no_exceptional_basepoint (p : Point) (hp : projection p = 0) :
    (∃ i, sectionValue (cubicSystem₁ i) p ≠ 0) ∧
    (∃ i, sectionValue (cubicSystem₂ i) p ≠ 0) ∧
    (∃ i, sectionValue (cubicSystem₃ i) p ≠ 0) ∧
    (∃ i, sectionValue (cubicSystem₄ i) p ≠ 0) := by
  simpa only [ne_eq,sectionValue_zero_iff] using
    central_systems_no_exceptional_basepoint p hp

/-- The nearby pencil likewise generates every exceptional fibre when t ≠ 0. -/
theorem nearby_actual_sections_no_exceptional_basepoint (t : ℂ) (ht : t ≠ 0)
    (p : Point) (hp : projection p = 0) :
    (∃ i, sectionValue (FailureOfSemipositiveMetricExtension.PencilSections.pencilSystem₁ t i) p ≠ 0) ∧
    (∃ i, sectionValue (FailureOfSemipositiveMetricExtension.PencilSections.pencilSystem₂ t i) p ≠ 0) ∧
    (∃ i, sectionValue (FailureOfSemipositiveMetricExtension.PencilSections.pencilSystem₃ t i) p ≠ 0) ∧
    (∃ i, sectionValue (FailureOfSemipositiveMetricExtension.PencilSections.pencilSystem₄ t i) p ≠ 0) := by
  simpa only [ne_eq,sectionValue_zero_iff] using
    FailureOfSemipositiveMetricExtension.PencilSections.nearby_systems_no_exceptional_basepoint t ht p hp
end
end FailureOfSemipositiveMetricExtension.BlowupLineBundle
