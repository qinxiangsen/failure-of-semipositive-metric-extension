import FailureOfSemipositiveMetricExtension.ProjectiveLineBundle
import FailureOfSemipositiveMetricExtension.ProjectiveLineMaps
import FailureOfSemipositiveMetricExtension.NegativeDegreeEntire

/-! Genuine analytic sections of the actual projective-line bundles and
vanishing in every negative integer degree. -/
namespace FailureOfSemipositiveMetricExtension.ProjectiveLineBundle
noncomputable section
open FailureOfSemipositiveMetricExtension.ProjectiveLine Set Bundle IsManifold
open scoped Manifold ContDiff Topology

structure SectionData (d : ℤ) where
  coefficient : Fin 2 → Point → ℂ
  analytic : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (coefficient i) (chartSet i)
  compatible : ∀ i j p, p ∈ chartSet i ∩ chartSet j →
    gain d i j p * coefficient i p = coefficient j p

def sectionValue {d : ℤ} (s : SectionData d) (p : Point) : (core d).Fiber p :=
  s.coefficient ((core d).indexAt p) p

def sectionMap {d : ℤ} (s : SectionData d) : Point → (core d).TotalSpace :=
  fun p => ⟨p,sectionValue s p⟩

theorem sectionMap_localTriv {d : ℤ} (s : SectionData d) (i : Fin 2) (p : Point)
    (hp : p ∈ chartSet i) : (core d).localTriv i (sectionMap s p) = (p,s.coefficient i p) := by
  rw [VectorBundleCore.localTriv_apply]
  congr 1
  exact s.compatible ((core d).indexAt p) i p ⟨(core d).mem_baseSet_at p,hp⟩

theorem sectionMap_contMDiff {d : ℤ} (s : SectionData d) :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (sectionMap s) := by
  intro p
  let i := (core d).indexAt p
  let e := (core d).localTriv i
  haveI : MemTrivializationAtlas e := ⟨⟨i,rfl⟩⟩
  have hp : p ∈ chartSet i := (core d).mem_baseSet_at p
  apply (e.contMDiffAt_iff (show sectionMap s p ∈ e.source from hp)).mpr
  refine ⟨contMDiffAt_id,?_⟩
  exact ((s.analytic i).congr (fun q hq => congrArg Prod.snd
    (sectionMap_localTriv s i q hq))).contMDiffAt ((chartSet_isOpen i).mem_nhds hp)

def chartCoefficient {d : ℤ} (s : SectionData d) (i : Fin 2) (z : ℂ) : ℂ :=
  s.coefficient i (param i z)

theorem chartCoefficient_contDiff {d : ℤ} (s : SectionData d) (i : Fin 2) :
    ContDiff ℂ ω (chartCoefficient s i) :=
  ((s.analytic i).comp_contMDiff (param_contMDiff i ω) (fun z => ⟨z,rfl⟩)).contDiff

theorem chartCoefficient_transition {d : ℤ} (s : SectionData d) (z : ℂ) (hz : z ≠ 0) :
    chartCoefficient s 0 z = z^d * chartCoefficient s 1 z⁻¹ := by
  have he : param 0 z = param 1 z⁻¹ := by
    simpa only [transition,ite_false] using param_transition 0 1 z (by simpa [overlap] using hz)
  have hp1 : param 0 z ∈ chartSet 1 := by rw [he]; exact ⟨z⁻¹,rfl⟩
  have h := s.compatible 1 0 (param 0 z) ⟨hp1,⟨z,rfl⟩⟩
  simpa only [gain,ratio,show (1:Fin 2) ≠ 0 by decide,if_false,coordinates_param,
    chartCoefficient,← he] using h.symm

theorem negative_coefficient_zero (k : ℕ) (s : SectionData (Int.negSucc k)) :
    ∀ i p, p ∈ chartSet i → s.coefficient i p = 0 := by
  have hf := FailureOfSemipositiveMetricExtension.negative_degree_entire_pair k (chartCoefficient s 0) (chartCoefficient s 1)
    ((chartCoefficient_contDiff s 0).differentiable (by simp))
    (chartCoefficient_contDiff s 1).continuous (by
      intro z hz
      simpa only [zpow_negSucc,inv_pow] using chartCoefficient_transition s z hz)
  intro i p hp
  obtain ⟨z,rfl⟩ := hp
  fin_cases i
  · exact hf.1 z
  · exact hf.2 z

/-- Actual global sections of every negative-degree bundle vanish identically. -/
theorem negative_sectionValue_zero (d : ℤ) (hd : d < 0) (s : SectionData d) (p : Point) :
    sectionValue s p = 0 := by
  cases d with
  | ofNat k => exact (not_lt_of_ge (Int.ofNat_nonneg k) hd).elim
  | negSucc k =>
    exact negative_coefficient_zero k s ((core (Int.negSucc k)).indexAt p) p
      ((core (Int.negSucc k)).mem_baseSet_at p)

/-- Every genuine analytic section of the actual bundle supplies compatible
holomorphic coefficients in its actual trivializations. -/
def ofAnalyticSection {d : ℤ} (s : ∀ p : Point, (core d).Fiber p)
    (hs : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (fun p => (⟨p,s p⟩ : (core d).TotalSpace))) :
    SectionData d where
  coefficient i p := ((core d).localTriv i ⟨p,s p⟩).2
  analytic i := by
    let e := (core d).localTriv i
    haveI : MemTrivializationAtlas e := ⟨⟨i,rfl⟩⟩
    have hh : ContMDiffOn 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω
        (fun p => e (⟨p,s p⟩ : (core d).TotalSpace)) (chartSet i) :=
      e.contMDiffOn.comp hs.contMDiffOn (fun p hp => hp)
    exact contMDiff_snd.comp_contMDiffOn hh
  compatible i j p hp := by
    change gain d i j p * (gain d ((core d).indexAt p) i p * (show ℂ from s p)) =
      gain d ((core d).indexAt p) j p * (show ℂ from s p)
    rw [← mul_assoc,gain_comp d ((core d).indexAt p) i j p
      ⟨⟨(core d).mem_baseSet_at p,hp.1⟩,hp.2⟩]

theorem ofAnalyticSection_value {d : ℤ} (s : ∀ p : Point, (core d).Fiber p)
    (hs : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (fun p => (⟨p,s p⟩ : (core d).TotalSpace)))
    (p : Point) : sectionValue (ofAnalyticSection s hs) p = s p := by
  change gain d ((core d).indexAt p) ((core d).indexAt p) p * (show ℂ from s p) = s p
  simp [gain,ratio_self]

/-- Vanishing of arbitrary actual analytic sections, not merely user-supplied
coefficient data. This is the geometric O(d<0) vanishing theorem. -/
theorem analytic_section_zero (d : ℤ) (hd : d < 0) (s : ∀ p : Point, (core d).Fiber p)
    (hs : ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω (fun p => (⟨p,s p⟩ : (core d).TotalSpace)))
    (p : Point) : s p = 0 := by
  rw [← ofAnalyticSection_value s hs p]
  exact negative_sectionValue_zero d hd (ofAnalyticSection s hs) p

end
end FailureOfSemipositiveMetricExtension.ProjectiveLineBundle
