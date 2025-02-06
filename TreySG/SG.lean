import Mathlib.Data.Set.Basic

namespace SG

section SG

structure Lane : Type where
(id : Nat)
deriving Repr

structure Vehicle : Type where
(id : Nat)
deriving Repr

structure StopSign : Type where
(id : Nat)

structure SG : Type 1 where
(lanes : Set Lane)
(egoVehicle : Vehicle)
(otherVehicles : Set Vechicle)
(egoInvariant : egoVehicle ∉ otherVehicles)
(stopSigns : Set StopSign)
(ssControlsLane : StopSign → Lane → Bool)
(vehInLane : Vehicle → Lane → Bool)
(hasStop : Prop :=
  let egoLanes := { l : Lane | vehInLane egoVehicle l}
  let lanesWithSS := { l : Lane | ∃ s ∈ stopSigns, ssControlsLane s l }
  egoLanes ∩ lanesWithSS ≠ {})



end SG

end SG
