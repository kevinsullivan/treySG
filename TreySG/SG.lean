import Mathlib.Data.Set.Basic

namespace TreySG.SG

-- Entity Types

structure Lane : Type where
(id : Nat)
deriving Repr

structure Vehicle : Type where
(id : Nat)
deriving Repr

structure StopSign : Type where
(id : Nat)

structure TreySceneGraph : Type 1 where
(lanes : Set Lane)
(egoVehicle : Vehicle)
(otherVehicles : Set Vechicle)
(egoNotOther : egoVehicle ∉ otherVehicles)
(vehicles : Set Vehicle := { egoVehicle} ∪ otherVehicles)
(stopSigns : Set StopSign)
(ssControlsLane : StopSign → Lane → Bool)
(vehInLane : Vehicle → Lane → Bool)

-- properties

structure TreyFormulaProperties : Type _ where
(sg : TreySceneGraph)
(lanesControledBySS : Set Lane := { l ∈ sg.lanes |  ∀ ss ∈ sg.stopSigns, sg.ssControlsLane ss l })
(vehicleLanes : Vehicle → Set Lane := λ v => { l ∈ sg.lanes | ∀ veh ∈ sg.vehicles, sg.vehInLane veh l})
(egoLanes : Set Lane := vehicleLanes sg.egoVehicle)
(vehHasStop (v : Vehicle) : Prop := ∃ l, l ∈ vehicleLanes v ∩ lanesControledBySS)
(egoHasStop : Prop := vehHasStop sg.egoVehicle)
(properties : List Prop := [egoHasStop])

end TreySG.SG
