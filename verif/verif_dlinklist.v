Require Import VST.floyd.proofauto.
Require Import DL.verif.dlinklist.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.