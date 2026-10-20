import FailureOfSemipositiveMetricExtension.CaoTotalFormAdapter
import FailureOfSemipositiveMetricExtension.AdjointSectionNonextension

/-! Genuine contraction by dt agrees with the already verified adjoint-section
restriction. The normal-first convention has positive sign in complex fibre
dimension two. This connects an actual alternating-form extension directly to
the existing, unconditional geometric nonextension obstruction. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
noncomputable section
open Set Bundle IsManifold TopologicalSpace
open scoped Manifold ContDiff

/-- Contracting the genuine Cao output yields exactly the existing central
coefficient, in every valid refined frame. -/
theorem extractSection_restrictsByDt {U : Opens Total} (S : TotalSection U)
    (s : CentralData)
    (h : CaoExtensionInterface.RestrictsByDt family fourthPowerLine S (centralSection s))
    (d : PowerIndex) (p : Fiber 0) (hp : FixedFiber.inclusion 0 p ∈ U)
    (hd : p ∈ FixedFiberBundle.divisionPatch 0 d) :
    (extractSection S).coefficient d (FixedFiber.inclusion 0 p) = s.coefficient d p := by
  let B := FixedFiber.tangentBasis 0 d.1 d.2.1 p hd.1
  let n := GlobalCanonical.normalVector d.1 d.2.1 (FixedFiber.inclusion 0 p) hd.1
  have hn := GlobalCanonical.normalVector_projection d.1 d.2.1 (FixedFiber.inclusion 0 p) hd.1
  let v : Fin 3 → TangentSpace 𝓘(ℂ,ChartCoord) (FixedFiber.inclusion 0 p) :=
    Matrix.vecCons n (fun k => mfderiv 𝓘(ℂ,FixedFiber.Coord) 𝓘(ℂ,ChartCoord)
      (FixedFiber.inclusion 0) p (B k))
  have hB : FixedFiber.tangentCoordinateForm 0 d.1 d.2.1 p B = 1 := by
    rw [FixedFiber.tangentCoordinateForm_eq_basis_det 0 d.1 d.2.1 p hd.1]
    exact Basis.det_self _
  have hv : GlobalCanonical.tangentCoordinateForm d.1 d.2.1 (FixedFiber.inclusion 0 p) v = 1 := by
    have hvol := congrArg (fun f => f B)
      (GlobalCanonical.tangentCoordinateForm_contraction 0 d.1 d.2.1 p hd.1 n hn)
    change GlobalCanonical.tangentCoordinateForm d.1 d.2.1 (FixedFiber.inclusion 0 p) v =
      FixedFiber.tangentCoordinateForm 0 d.1 d.2.1 p B at hvol
    exact hvol.trans hB
  have he := congrArg (fun f => (powerCore.localTriv d ⟨FixedFiber.inclusion 0 p,f B⟩).2)
    (h p n hn)
  change (powerCore.localTriv d ⟨FixedFiber.inclusion 0 p,S.form (FixedFiber.inclusion 0 p) v⟩).2 =
    (powerCore.localTriv d ⟨FixedFiber.inclusion 0 p,centralForm s p B⟩).2 at he
  rw [totalSection_represents S d (FixedFiber.inclusion 0 p) hp hd v,
    centralForm_localTriv s d p hd B,hv,hB,mul_one,mul_one] at he
  exact he

/-- Equality of the actual central adjoint fibre values, not merely agreement of
formal local symbols. -/
theorem extractSection_restriction_value {U : Opens Total} (S : TotalSection U)
    (s : CentralData)
    (h : CaoExtensionInterface.RestrictsByDt family fourthPowerLine S (centralSection s))
    (hU : ∀ p : Fiber 0, FixedFiber.inclusion 0 p ∈ U) (p : Fiber 0) :
    FixedFiberBundle.adjointSectionValue (GlobalAdjoint.restriction (extractSection S) 0 hU) p =
      FixedFiberBundle.adjointSectionValue s p :=
  extractSection_restrictsByDt S s h ((FixedFiberBundle.adjointCore 0 4).indexAt p) p
    (hU p) ((FixedFiberBundle.adjointCore 0 4).mem_baseSet_at p)

/-- The previously proved section obstruction now applies to the precise actual
L⁴-valued top forms used by the generic literature interface. -/
theorem sigmaCentralSection_no_extension (U : Opens Total)
    (hU : ∀ p : Fiber 0, FixedFiber.inclusion 0 p ∈ U) :
    ¬ ∃ S : TotalSection U,
      CaoExtensionInterface.RestrictsByDt family fourthPowerLine S sigmaCentralSection := by
  rintro ⟨S,hS⟩
  apply GlobalAdjoint.sigma_adjoint_has_no_neighbourhood_extension U hU
  refine ⟨extractSection S,?_⟩
  intro d p hd
  exact extractSection_restrictsByDt S FixedFiberBundle.sigmaAdjointData hS d p (hU p) hd

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.CaoAdapter
