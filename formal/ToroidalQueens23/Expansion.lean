import ToroidalQueens23.Kernels
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace ToroidalQueens23
noncomputable section


theorem degree_add_bound {a b : Poly} {n : Nat}
    (ha : a.totalDegree ≤ n) (hb : b.totalDegree ≤ n) :
    (a+b).totalDegree ≤ n := (MvPolynomial.totalDegree_add _ _).trans (max_le ha hb)

theorem degree_pow_bound {z : Poly} (hz : z.totalDegree ≤ 1) (n : Nat) :
    (z^n).totalDegree ≤ n := by
  simpa using (MvPolynomial.totalDegree_pow z n).trans (Nat.mul_le_mul_left n hz)

theorem degree_C_pow_bound {z : Poly} (hz : z.totalDegree ≤ 1) (c : F) (n : Nat) :
    (MvPolynomial.C c*z^n).totalDegree ≤ n := by
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using degree_pow_bound hz n)

def jetB (z : Poly) (u v : F) (e : Poly) : Poly :=
  MvPolynomial.C u*z^9+MvPolynomial.C v*z^8+e

def jet (z : Poly) (u v : F) (e : Poly) : Poly := z^11+jetB z u v e

theorem jetB_degree {z e : Poly} (hz : z.totalDegree ≤ 1) (he : e.totalDegree ≤ 7)
    (u v : F) : (jetB z u v e).totalDegree ≤ 9 := by
  exact degree_add_bound (degree_add_bound (degree_C_pow_bound hz u 9)
    ((degree_C_pow_bound hz v 8).trans (by decide))) (he.trans (by decide))

def jetError (uR uC uS uD vR vC vS vD : F) (eR eC eS eD : Poly) : Poly :=
  eR*py^11*ps^11*pd^11+
  px^11*eC*ps^11*pd^11+
  px^11*py^11*eS*pd^11+
  px^11*py^11*ps^11*eD+
  (jetB px uR vR eR)*(jetB py uC vC eC)*ps^11*pd^11+
  (jetB px uR vR eR)*py^11*(jetB ps uS vS eS)*pd^11+
  (jetB px uR vR eR)*py^11*ps^11*(jetB pd uD vD eD)+
  px^11*(jetB py uC vC eC)*(jetB ps uS vS eS)*pd^11+
  px^11*(jetB py uC vC eC)*ps^11*(jetB pd uD vD eD)+
  px^11*py^11*(jetB ps uS vS eS)*(jetB pd uD vD eD)+
  (jetB px uR vR eR)*(jetB py uC vC eC)*(jetB ps uS vS eS)*pd^11+
  (jetB px uR vR eR)*(jetB py uC vC eC)*ps^11*(jetB pd uD vD eD)+
  (jetB px uR vR eR)*py^11*(jetB ps uS vS eS)*(jetB pd uD vD eD)+
  px^11*(jetB py uC vC eC)*(jetB ps uS vS eS)*(jetB pd uD vD eD)+
  (jetB px uR vR eR)*(jetB py uC vC eC)*(jetB ps uS vS eS)*(jetB pd uD vD eD)

theorem jetError_degree (uR uC uS uD vR vC vS vD : F) (eR eC eS eD : Poly)
    (heR : eR.totalDegree ≤ 7) (heC : eC.totalDegree ≤ 7)
    (heS : eS.totalDegree ≤ 7) (heD : eD.totalDegree ≤ 7) :
    (jetError uR uC uS uD vR vC vS vD eR eC eS eD).totalDegree ≤ 40 := by
  unfold jetError
  apply degree_add_bound
  · apply degree_add_bound
    · apply degree_add_bound
      · apply degree_add_bound
        · apply degree_add_bound
          · apply degree_add_bound
            · apply degree_add_bound
              · apply degree_add_bound
                · apply degree_add_bound
                  · apply degree_add_bound
                    · apply degree_add_bound
                      · apply degree_add_bound
                        · apply degree_add_bound
                          · apply degree_add_bound
                            · exact (degree_four heR (degree_pow_bound py_degree 11) (degree_pow_bound ps_degree 11) (degree_pow_bound pd_degree 11)).trans (by decide)
                            · exact (degree_four (degree_pow_bound px_degree 11) heC (degree_pow_bound ps_degree 11) (degree_pow_bound pd_degree 11)).trans (by decide)
                          · exact (degree_four (degree_pow_bound px_degree 11) (degree_pow_bound py_degree 11) heS (degree_pow_bound pd_degree 11)).trans (by decide)
                        · exact (degree_four (degree_pow_bound px_degree 11) (degree_pow_bound py_degree 11) (degree_pow_bound ps_degree 11) heD).trans (by decide)
                      · exact (degree_four (jetB_degree px_degree heR uR vR) (jetB_degree py_degree heC uC vC) (degree_pow_bound ps_degree 11) (degree_pow_bound pd_degree 11)).trans (by decide)
                    · exact (degree_four (jetB_degree px_degree heR uR vR) (degree_pow_bound py_degree 11) (jetB_degree ps_degree heS uS vS) (degree_pow_bound pd_degree 11)).trans (by decide)
                  · exact (degree_four (jetB_degree px_degree heR uR vR) (degree_pow_bound py_degree 11) (degree_pow_bound ps_degree 11) (jetB_degree pd_degree heD uD vD)).trans (by decide)
                · exact (degree_four (degree_pow_bound px_degree 11) (jetB_degree py_degree heC uC vC) (jetB_degree ps_degree heS uS vS) (degree_pow_bound pd_degree 11)).trans (by decide)
              · exact (degree_four (degree_pow_bound px_degree 11) (jetB_degree py_degree heC uC vC) (degree_pow_bound ps_degree 11) (jetB_degree pd_degree heD uD vD)).trans (by decide)
            · exact (degree_four (degree_pow_bound px_degree 11) (degree_pow_bound py_degree 11) (jetB_degree ps_degree heS uS vS) (jetB_degree pd_degree heD uD vD)).trans (by decide)
          · exact (degree_four (jetB_degree px_degree heR uR vR) (jetB_degree py_degree heC uC vC) (jetB_degree ps_degree heS uS vS) (degree_pow_bound pd_degree 11)).trans (by decide)
        · exact (degree_four (jetB_degree px_degree heR uR vR) (jetB_degree py_degree heC uC vC) (degree_pow_bound ps_degree 11) (jetB_degree pd_degree heD uD vD)).trans (by decide)
      · exact (degree_four (jetB_degree px_degree heR uR vR) (degree_pow_bound py_degree 11) (jetB_degree ps_degree heS uS vS) (jetB_degree pd_degree heD uD vD)).trans (by decide)
    · exact (degree_four (degree_pow_bound px_degree 11) (jetB_degree py_degree heC uC vC) (jetB_degree ps_degree heS uS vS) (jetB_degree pd_degree heD uD vD)).trans (by decide)
  · exact (degree_four (jetB_degree px_degree heR uR vR) (jetB_degree py_degree heC uC vC) (jetB_degree ps_degree heS uS vS) (jetB_degree pd_degree heD uD vD)).trans (by decide)

theorem jet_product_expansion (uR uC uS uD vR vC vS vD : F) (eR eC eS eD : Poly) :
    (jet px uR vR eR)*(jet py uC vC eC)*(jet ps uS vS eS)*(jet pd uD vD eD) =
    topKernel+
    MvPolynomial.C uR*kernelR2+
    MvPolynomial.C uC*kernelC2+
    MvPolynomial.C uS*kernelS2+
    MvPolynomial.C uD*kernelD2+
    MvPolynomial.C vR*kernelR3+
    MvPolynomial.C vC*kernelC3+
    MvPolynomial.C vS*kernelS3+
    MvPolynomial.C vD*kernelD3+
    jetError uR uC uS uD vR vC vS vD eR eC eS eD := by
  simp only [jet,jetB,jetError,topKernel,kernelR2,kernelC2,kernelS2,kernelD2,kernelR3,kernelC3,kernelS3,kernelD3]
  ring

end
end ToroidalQueens23
