import FailureOfSemipositiveMetricExtension.GlobalAnalyticMaps

/-! Genuine exceptional projective lines and their analytic inclusion in the
constructed global family. Each exceptional fibre is homeomorphic to the actual
projective line, and the whole parametrized exceptional locus is analytic. -/

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section
open Set Topology
open scoped Manifold ContDiff

@[simp] theorem localParam_zero (e : Fin 2) (s : ℂ) :
    localParam e (0,s) = Blowup.exceptionalPoint (ProjectiveLine.param e s) := by
  apply Blowup.point_ext
  · fin_cases e <;> ext k <;> fin_cases k <;> simp [localParam,Blowup.projection,Blowup.X,Blowup.Y,Blowup.exceptionalPoint]
  · exact localParam_direction e (0,s)

@[simp] theorem localLift_exceptionalPoint (i : Fin 4) (t : ℂ) (d : Direction) :
    localLift i (Blowup.exceptionalPoint d) t = pointOverCentre i t d := by
  apply Subtype.ext
  simp [localLift,pointOverCentre,affineBase_zero]

/-- Exceptional points have radial coordinate zero in either actual blow-up chart. -/
@[simp] theorem chartParam_exceptional (i : Fin 4) (e : Fin 2) (s t : ℂ) :
    chartParam i e ((0,s),t) = pointOverCentre i t (ProjectiveLine.param e s) := by
  simp [chartParam]

/-- The entire exceptional line stays in the legitimate domain of its centre chart. -/
theorem exceptional_mem_chartDomain (i : Fin 4) (e : Fin 2) (s t : ℂ) :
    ((0,s),t) ∈ chartDomain i e := by
  intro j hj
  simp only [localParam_zero,Blowup.projection_exceptionalPoint,affineBase_zero]
  exact (centre_injective t).ne (Ne.symm hj)

/-- The joint map from the actual P¹ times the parameter line is complex analytic. -/
theorem pointOverCentre_joint_contMDiff (i : Fin 4) (n : WithTop ℕ∞) :
    ContMDiff (𝓘(ℂ).prod 𝓘(ℂ)) 𝓘(ℂ,ChartCoord) n
      (fun q : Direction × ℂ => pointOverCentre i q.2 q.1) := by
  intro q
  obtain ⟨e,s,hs⟩ := ProjectiveLine.charts_cover q.1
  have hq : q.1 ∈ ProjectiveLine.chartSet e := ⟨s,hs.symm⟩
  have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n (ProjectiveLine.coordinates e) q.1 :=
    (lineCoordinates_contMDiffOn e n).contMDiffAt
      ((ProjectiveLine.chartSet_isOpen e).mem_nhds hq)
  have hd : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) 𝓘(ℂ) n
      (fun q' : Direction × ℂ => ProjectiveLine.coordinates e q'.1) q :=
    hc.comp q contMDiffAt_fst
  have hv : ContMDiffAt (𝓘(ℂ).prod 𝓘(ℂ)) 𝓘(ℂ,ChartCoord) n
      (fun q' : Direction × ℂ => (((0 : ℂ),ProjectiveLine.coordinates e q'.1),q'.2)) q :=
    (contMDiffAt_const.prodMk_space hd).prodMk_space contMDiffAt_snd
  have ha := (chartParam_contMDiffOn i e n).contMDiffAt
    ((chartDomain_isOpen i e).mem_nhds
      (exceptional_mem_chartDomain i e (ProjectiveLine.coordinates e q.1) q.2))
  apply (ha.comp q hv).congr_of_eventuallyEq
  have hopen : IsOpen {q' : Direction × ℂ | q'.1 ∈ ProjectiveLine.chartSet e} :=
    (ProjectiveLine.chartSet_isOpen e).preimage continuous_fst
  filter_upwards [hopen.mem_nhds hq] with q' hq'
  dsimp only [Function.comp_apply]
  rw [chartParam_exceptional,ProjectiveLine.param_coordinates e q'.1 hq']

/-- Each fixed exceptional projective line maps analytically into the global manifold. -/
theorem pointOverCentre_contMDiff (i : Fin 4) (t : ℂ) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ,ChartCoord) n (pointOverCentre i t) :=
  (pointOverCentre_joint_contMDiff i n).comp (contMDiff_id.prodMk contMDiff_const)

theorem pointOverCentre_continuous (i : Fin 4) (t : ℂ) : Continuous (pointOverCentre i t) :=
  (pointOverCentre_contMDiff i t 0).continuous

/-- The actual exceptional fibre, with its inherited subspace topology, is P¹. -/
def exceptionalFiberHomeomorph (i : Fin 4) (t : ℂ) :
    {q : Total // blowdown q = centre i t ∧ projection q = t} ≃ₜ Direction where
  toEquiv := exceptionalFiberEquiv i t
  continuous_toFun := (direction_continuous i).comp continuous_subtype_val
  continuous_invFun := (pointOverCentre_continuous i t).subtype_mk (fun _ => ⟨rfl,rfl⟩)

/-- No compactness of the exceptional fibre is assumed: it follows from the actual P¹ model. -/
theorem exceptionalFiber_isCompact (i : Fin 4) (t : ℂ) :
    IsCompact {q : Total | blowdown q = centre i t ∧ projection q = t} := by
  have heq : {q : Total | blowdown q = centre i t ∧ projection q = t} =
      range (pointOverCentre i t) := by
    ext q
    constructor
    · intro hq
      exact ⟨directions q i,congrArg Subtype.val ((exceptionalFiberEquiv i t).left_inv ⟨q,hq⟩)⟩
    · rintro ⟨d,rfl⟩
      exact ⟨rfl,rfl⟩
  rw [heq]
  exact isCompact_range (pointOverCentre_continuous i t)

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
