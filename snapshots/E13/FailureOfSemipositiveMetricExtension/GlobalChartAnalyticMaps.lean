import FailureOfSemipositiveMetricExtension.GlobalChartTopology
import FailureOfSemipositiveMetricExtension.ProjectivePlaneFamily

/-!
Analytic coordinate-component maps of the eight global incidence parametrizations.
These assertions use the existing projective plane and projective line manifolds;
no manifold structure on the global incidence total space is assumed here.
-/

namespace FailureOfSemipositiveMetricExtension.GlobalIncidence
noncomputable section

open Set
open scoped Manifold ContDiff

/-- The projected affine blow-up parametrizations are polynomial maps. -/
theorem localParam_projection_contDiff (e : Fin 2) (n : WithTop ℕ∞) :
    ContDiff ℂ n (fun q : ℂ × ℂ => Blowup.projection (localParam e q)) := by
  apply contDiff_pi.mpr
  intro k
  fin_cases e <;> fin_cases k <;>
    dsimp [localParam,Blowup.projection,Blowup.X,Blowup.Y] <;> fun_prop

/-- Centred affine base coordinates are polynomial, including the moving centre. -/
theorem baseCoordinates_contDiff (i : Fin 4) (n : WithTop ℕ∞) :
    ContDiff ℂ n (fun q : ℂ × Blowup.Plane => baseCoordinates i q.1 q.2) := by
  fin_cases i <;> dsimp [baseCoordinates] <;> fun_prop

/-- The homogeneous representative in each normalized base chart varies polynomially. -/
theorem baseVector_contDiff (i : Fin 4) (n : WithTop ℕ∞) :
    ContDiff ℂ n (fun q : ℂ × Blowup.Plane => baseVector i q.1 q.2) := by
  apply contDiff_pi.mpr
  intro k
  fin_cases i <;> fin_cases k <;> dsimp [baseVector] <;> fun_prop

/-- All centre-ideal pairs are polynomial jointly in the family and homogeneous coordinates. -/
theorem pairMap_contDiff (j : Fin 4) (n : WithTop ℕ∞) :
    ContDiff ℂ n (fun q : ℂ × (Fin 3 → ℂ) => pairMap j q.1 q.2) := by
  apply contDiff_pi.mpr
  intro k
  fin_cases j <;> fin_cases k <;> dsimp [pairMap,pair] <;> fun_prop

/-- The normalized affine base is analytic into the actual projective plane. -/
theorem affineBase_contMDiff (i : Fin 4) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,ℂ × Blowup.Plane) 𝓘(ℂ,ℂ × ℂ) n
      (fun q : ℂ × Blowup.Plane => affineBase i q.1 q.2) := by
  simp_rw [affineBase_eq_param]
  exact (ProjectivePlane.param_contMDiff (baseChart i) n).comp
    (baseCoordinates_contDiff i n).contMDiff

/-- The global chart's projective base component is analytic on all coordinates. -/
theorem chartBase_contMDiff (i : Fin 4) (e : Fin 2) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ℂ × ℂ) n
      (fun q : ChartCoord => affineBase i q.2 (Blowup.projection (localParam e q.1))) :=
  (affineBase_contMDiff i n).comp
    (contDiff_snd.prodMk ((localParam_projection_contDiff e n).comp contDiff_fst)).contMDiff

/-- The blowdown component of every global parametrization is analytic. -/
theorem chartParam_blowdown_contMDiff (i : Fin 4) (e : Fin 2) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ℂ × ℂ) n
      (fun q => blowdown (chartParam i e q)) :=
  chartBase_contMDiff i e n

theorem chartParam_blowdown_contMDiffOn (i : Fin 4) (e : Fin 2) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ,ℂ × ℂ) n
      (fun q => blowdown (chartParam i e q)) (chartDomain i e) :=
  (chartParam_blowdown_contMDiff i e n).contMDiffOn

set_option maxHeartbeats 1000000 in
/-- The polynomial vectors that produce the three other projective directions. -/
theorem chartPair_contDiff (i : Fin 4) (e : Fin 2) (j : Fin 4) (n : WithTop ℕ∞) :
    ContDiff ℂ n (chartPair i e j) :=
  (pairMap_contDiff j n).comp (contDiff_snd.prodMk ((baseVector_contDiff i n).comp
    (contDiff_snd.prodMk ((localParam_projection_contDiff e n).comp contDiff_fst))))

/-- All four projective direction components are analytic on each global chart domain. -/
theorem chartParam_direction_contMDiffOn (i : Fin 4) (e : Fin 2) (j : Fin 4)
    (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) n
      (fun q => directions (chartParam i e q) j) (chartDomain i e) := by
  by_cases hj : j = i
  · subst j
    simp only [chartParam,localLift_direction,localParam_direction]
    exact ((ProjectiveLine.param_contMDiff e n).comp
      (contDiff_snd.comp contDiff_fst).contMDiff).contMDiffOn
  · have hc := (ProjectiveLine.vectorPoint_contMDiffOn n).comp
      (chartPair_contDiff i e j n).contMDiff.contMDiffOn
      (fun q hq => chartPair_ne_zero i e j q hq hj)
    apply hc.congr
    intro q hq
    change (if j = i then _ else _) = _
    simp only [hj,ite_false]
    exact chosenDirection_affineBase_eq_vectorPoint i j q.2 _ (hq j hj)

/-- The family component in each global chart is the last affine coordinate. -/
theorem chartParam_projection_contDiff (i : Fin 4) (e : Fin 2) (n : WithTop ℕ∞) :
    ContDiff ℂ n (fun q : ChartCoord => projection (chartParam i e q)) :=
  contDiff_snd

theorem chartParam_projection_contMDiff (i : Fin 4) (e : Fin 2) (n : WithTop ℕ∞) :
    ContMDiff 𝓘(ℂ,ChartCoord) 𝓘(ℂ) n
      (fun q => projection (chartParam i e q)) :=
  (chartParam_projection_contDiff i e n).contMDiff

theorem chartParam_projection_contMDiffOn (i : Fin 4) (e : Fin 2) (n : WithTop ℕ∞) :
    ContMDiffOn 𝓘(ℂ,ChartCoord) 𝓘(ℂ) n
      (fun q => projection (chartParam i e q)) (chartDomain i e) :=
  (chartParam_projection_contMDiff i e n).contMDiffOn

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence
