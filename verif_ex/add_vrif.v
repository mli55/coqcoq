Require Import VST.floyd.proofauto.
(** This file is auxiliary tactics that we will use in this tutorial. *)
Require Export VST.floyd.Funspec_old_Notation.

(** These are the C programs that we will verify. *)
Require EV.add EV.abs EV.append EV.max3 EV.swap EV.tri EV.gcd EV.fact EV.test_null EV.reverse.

Local Open Scope logic.

Module Verif_uadd.