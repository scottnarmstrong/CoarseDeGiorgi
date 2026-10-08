module

public import CoarseDeGiorgi.Statements.WeakHarnack
public import CoarseDeGiorgi.Harnack.Final.Harnack

@[expose] public section

namespace CoarseDeGiorgi

theorem harnack_proved :
    type_of% (Harnack.Final.harnack_proved CoarseDeGiorgi.weak_harnack) :=
  Harnack.Final.harnack_proved CoarseDeGiorgi.weak_harnack

end CoarseDeGiorgi
