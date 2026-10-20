import FailureOfSemipositiveMetricExtension.CaoCentralFormAdapter
import FailureOfSemipositiveMetricExtension.GlobalAdjointSections

/-! A genuine extended L⁴-valued three-form determines a section of the existing
actual total adjoint bundle. Diagonal coordinate/frame extraction is justified
by the representation equation, the true frame law, and a tangent basis. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
noncomputable section
open Set Bundle IsManifold TopologicalSpace
open scoped Manifold ContDiff

abbrev TotalSection (U : Opens Total) :=
  CaoExtensionInterface.TotalAdjointSection family fourthPowerLine U

theorem power_localTriv_transition (d c : PowerIndex) (p : Total)
    (hd : p ∈ powerCore.baseSet d) (hc : p ∈ powerCore.baseSet c) (v : powerCore.Fiber p) :
    powerGain d c p * (powerCore.localTriv d ⟨p,v⟩).2 =
      (powerCore.localTriv c ⟨p,v⟩).2 := by
  rw [VectorBundleCore.localTriv_apply,VectorBundleCore.localTriv_apply]
  exact powerCore.coordChange_comp (powerCore.indexAt p) d c p
    ⟨⟨powerCore.mem_baseSet_at p,hd⟩,hc⟩ v

theorem totalSection_represents {U : Opens Total} (S : TotalSection U)
    (d : PowerIndex) (p : Total) (hp : p ∈ U) (hd : p ∈ GlobalAdjoint.patch d)
    (v : Fin 3 → TangentSpace 𝓘(ℂ,ChartCoord) p) :
    (powerCore.localTriv d ⟨p,S.form p v⟩).2 =
      S.coefficient (GlobalAdjoint.chart d) d p * GlobalCanonical.tangentCoordinateForm d.1 d.2.1 p v :=
  S.represents (GlobalAdjoint.chart d) d p ⟨⟨hd.1,hd⟩,hp⟩ v

theorem diagonal_coefficient_compatible {U : Opens Total} (S : TotalSection U)
    (d c : PowerIndex) (p : Total) (hp : p ∈ U)
    (hd : p ∈ GlobalAdjoint.patch d) (hc : p ∈ GlobalAdjoint.patch c) :
    GlobalAdjoint.gain 4 d c p * S.coefficient (GlobalAdjoint.chart d) d p =
      S.coefficient (GlobalAdjoint.chart c) c p := by
  let B := GlobalCanonical.tangentBasis c.1 c.2.1 p hc.1
  have hB : GlobalCanonical.tangentCoordinateForm c.1 c.2.1 p B = 1 := by
    rw [GlobalCanonical.tangentCoordinateForm_eq_basis_det c.1 c.2.1 p hc.1]
    exact Basis.det_self _
  have hD : GlobalCanonical.tangentCoordinateForm d.1 d.2.1 p B =
      GlobalCanonical.canonicalGain (GlobalAdjoint.chart d) (GlobalAdjoint.chart c) p := by
    have hf : GlobalCanonical.tangentCoordinateForm d.1 d.2.1 p =
        GlobalCanonical.canonicalGain (GlobalAdjoint.chart d) (GlobalAdjoint.chart c) p •
          GlobalCanonical.tangentCoordinateForm c.1 c.2.1 p :=
      GlobalCanonical.tangentCoordinateForm_canonicalGain (GlobalAdjoint.chart d)
        (GlobalAdjoint.chart c) p hd.1 hc.1
    rw [hf]
    simp only [AlternatingMap.smul_apply,smul_eq_mul,hB,mul_one]
  have h := power_localTriv_transition d c p hd hc (S.form p B)
  rw [totalSection_represents S d p hp hd B,totalSection_represents S c p hp hc B,hB,hD,mul_one] at h
  change (GlobalCanonical.canonicalGain (GlobalAdjoint.chart d) (GlobalAdjoint.chart c) p *
    powerGain d c p) * S.coefficient (GlobalAdjoint.chart d) d p = _
  calc
    _ = powerGain d c p * (S.coefficient (GlobalAdjoint.chart d) d p *
      GlobalCanonical.canonicalGain (GlobalAdjoint.chart d) (GlobalAdjoint.chart c) p) := by ring
    _ = _ := h

/-- Conversion of an actual Cao output to the actual pre-existing K_Total⊗L⁴
section. Its compatibility is proved, not supplied as extra input. -/
def extractSection {U : Opens Total} (S : TotalSection U) : GlobalAdjoint.SectionOn U 4 where
  coefficient d := S.coefficient (GlobalAdjoint.chart d) d
  analytic d := (S.analytic (GlobalAdjoint.chart d) d).mono
    (show GlobalAdjoint.patch d ∩ U ⊆
      (CaoExtensionInterface.totalPatch family fourthPowerLine U (GlobalAdjoint.chart d) d : Set Total) from
        fun p hp => ⟨⟨hp.1.1,hp.1⟩,hp.2⟩)
  compatible := diagonal_coefficient_compatible S

@[simp] theorem extractSection_coefficient {U : Opens Total} (S : TotalSection U)
    (d : PowerIndex) (p : Total) :
    (extractSection S).coefficient d p = S.coefficient (GlobalAdjoint.chart d) d p := rfl

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
