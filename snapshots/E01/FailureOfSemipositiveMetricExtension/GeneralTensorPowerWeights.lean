import FailureOfSemipositiveMetricExtension.GeneralTensorPowerLine

/-! Actual tensor-power metric normalization and genuine multiplier-germ
identification for every positive integer exponent. -/
namespace FailureOfSemipositiveMetricExtension.GeneralCao
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff TensorProduct ENNReal

variable {n : ℕ} {M N : Type} [TopologicalSpace M] [ChartedSpace (Coord (n+1)) M]
    [TopologicalSpace N] [ChartedSpace (Coord n) N]
    {A B J : Type} (G : Family n M N A B) (L : AnalyticLine n (M := M) J)
    (h : SemipositiveWeight n G L)

def SemipositiveWeight.power (m : ℕ) (hm : 0 < m) : SemipositiveWeight n G (L.powerLine m) where
  weight i p := scaleWeight (m : ℝ) (h.weight i p)
  compatible i j p hp := by
    rw [h.compatible i j p hp,scaleWeight_add_real]
    change _ = _ + ((Real.log (Complex.normSq (L.gain i j p ^ m)) : ℝ) : WithBot ℝ)
    rw [map_pow,Real.log_pow]
  psh b i := (h.psh b i).scale_ge_one
    ((G.totalAtlas.chart b).symm.isOpen_inter_preimage (L.core.isOpen_baseSet i))
    (m : ℝ) (by exact_mod_cast hm)
  finite_points_dense i p hp := by
    simpa only [AnalyticLine.powerLine,AnalyticLine.powerCore,ne_eq,scaleWeight_eq_bot_iff] using h.finite_points_dense i p hp

theorem SemipositiveWeight.power_wellDefined (hw : RestrictionWellDefined n G L h)
    (m : ℕ) (hm : 0 < m) : RestrictionWellDefined n G (L.powerLine m) (h.power G L m hm) := by
  intro p
  obtain ⟨q,hq,i,hi,hfinite⟩ := hw p
  exact ⟨q,hq,i,hi,by simpa only [SemipositiveWeight.power,ne_eq,scaleWeight_eq_bot_iff] using hfinite⟩

/-- Original h^m multiplier density, applied to a section of the actual power line. -/
def InPowerRestrictedMultiplier (m : ℕ) (s : CentralAdjointSection n G (L.powerLine m)) : Prop :=
  ∀ (a : A) (i : J) (p : N) (hp : p ∈ centralPatch n G (L.powerLine m) a i),
    GeneralMultiplier.IntegrableGerm n N m (fun q => h.weight i (G.inclusion q)) p
      ((GeneralMultiplier.sheaf n N).presheaf.germ (centralPatch n G (L.powerLine m) a i) p hp
        (centralCoefficientSection n G (L.powerLine m) s a i))

theorem power_restrictedMultiplier_iff (m : ℕ) (hm : 0 < m)
    (s : CentralAdjointSection n G (L.powerLine m)) :
    InRestrictedMultiplier n G (L.powerLine m) (h.power G L m hm) s ↔
      InPowerRestrictedMultiplier G L h m s := by
  simp only [InRestrictedMultiplier,InPowerRestrictedMultiplier,SemipositiveWeight.power,
    GeneralMultiplier.integrableGerm_scale_nat_iff n N m hm]

theorem tensor_metric_density_pure (m : ℕ) (hm : 0 < m) (v : Fin m → ℂ) (u : WithBot ℝ) :
    ENNReal.ofReal (Complex.normSq (scalarTensorEquiv m (PiTensorProduct.tprod ℂ v))) *
      Multiplier.exponentialWeight (scaleWeight (m : ℝ) u) =
        ∏ k, (ENNReal.ofReal (Complex.normSq (v k)) * Multiplier.exponentialWeight u) := by
  rw [scalarTensorEquiv_pure,GeneralMultiplier.exponentialWeight_scale_nat m hm,
    map_prod,ENNReal.ofReal_prod_of_nonneg (fun i _ => Complex.normSq_nonneg (v i)),Finset.prod_mul_distrib]
  simp

theorem tensor_pure_frame (m : ℕ) (i : J) (p : M) (v : Fin m → L.core.Fiber p) :
    ((L.powerCore m).localTriv i ⟨p,L.tensorFiberEquiv m p (PiTensorProduct.tprod ℂ v)⟩).2 =
      ∏ k, (L.core.localTriv i ⟨p,v k⟩).2 := by
  simp only [VectorBundleCore.localTriv_apply,AnalyticLine.powerCore,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul,L.coordChange_eq,
    AnalyticLine.tensorFiberEquiv,scalarTensorEquiv_pure,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]
  exact congrArg (fun z : ℂ => L.gain (L.core.indexAt p) i p ^ m * z) (scalarTensorEquiv_pure m v)

end
end FailureOfSemipositiveMetricExtension.GeneralCao
