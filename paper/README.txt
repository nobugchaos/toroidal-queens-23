English preprint draft
Title: The independent domination number of the 23 by 23 toroidal queens graph:
a computer-assisted proof and Lean formalization
Author: Weixin Yu
Affiliation: Independent Researcher
Contact: iweixin1214@gmail.com
Date: November8,2026

The main.tex source is self-contained and uses standard LaTeX packages.
Compile using a current TeX Live/MiKTeX LaTeX installation, for example:
  pdflatex main.tex
  pdflatex main.tex
Tectonic can also compile it. There is no external bibliography tool or image
dependency. The plain theorem displays in the listings use ASCII logical
notation for readability; the actual compilable Unicode statements are in the
accompanying Lean source.

The manuscript covers the COMPLETE fixed-instance mathematical result
i(Q_23^t)=12, including its analytic proof, exhaustive computation, Lean
formalization and native computation trust. It is not a general-n solution.

The work has not been submitted to arXiv, assigned an arXiv identifier, or
externally peer reviewed. Literature priority is not claimed. The author
should perform final scholarly review and complete the comparison with older
literature before deciding whether and where to submit.

The Lean/native trust boundary is not an unfinished proof obligation: the
full theorem compiles with three explicitly reported native_decide generated
axioms in addition to Lean's standard axioms. A different goal, a proof using
only standard axioms and pure kernel evaluation, is not claimed to be achieved.

The source bundle includes the tested proof files and audit records. The large
historical LRAT archives are supplementary workspace evidence and are not
needed for the Lean proof or the LaTeX paper; they are not included in the
compact reproducibility bundle.
