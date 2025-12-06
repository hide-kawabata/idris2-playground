
data DoorCmdND : Type -> Type where
    OpenND : DoorCmdND Unit
    CloseND : DoorCmdND Unit
    RingBellND : DoorCmdND Unit

    PureND : ty -> DoorCmdND ty
    BindND : DoorCmdND a -> (a -> DoorCmdND b) -> DoorCmdND b
    SeqND : DoorCmdND Unit -> DoorCmdND b -> DoorCmdND b

namespace DoorCmdND
    export
    (>>=) : DoorCmdND a -> (a -> DoorCmdND b) -> DoorCmdND b
    (>>=) = BindND
    export
    (>>) : DoorCmdND Unit -> DoorCmdND b -> DoorCmdND b
    (>>) = SeqND

-- example of DoorCmdND program
doorProgND : DoorCmdND Unit
doorProgND = do RingBellND
                OpenND
                OpenND  -- no error
                CloseND -- no error
                CloseND


data DoorState = DoorClosed | DoorOpen -- defines the two possible states of a door

data DoorCmd : Type ->      -- the type of the result of the operation
               DoorState -> -- the state of the door before the operation
               DoorState -> -- the state of the door after the operation
               Type where
     OpenDoor : DoorCmd Unit DoorClosed DoorOpen
     Close : DoorCmd Unit DoorOpen DoorClosed
     RingBell : DoorCmd Unit DoorClosed DoorClosed

     Pure : ty -> DoorCmd ty state state
     Bind : DoorCmd a state1 state2 ->
             (a -> DoorCmd b state2 state3) -> 
             DoorCmd b state1 state3 -- combined operation
     Seq : DoorCmd Unit state1 state2 -> DoorCmd b state2 state3 -> 
             DoorCmd b state1 state3

namespace DoorCmd
    export
    (>>=) : DoorCmd a state1 state2 ->
             (a -> DoorCmd b state2 state3) -> 
             DoorCmd b state1 state3
    (>>=) = Bind
    export
    (>>) : DoorCmd Unit state1 state2 -> DoorCmd b state2 state3 -> 
             DoorCmd b state1 state3
    (>>) = Seq

-- example of DoorCmd program
doorProg : DoorCmd Unit DoorClosed DoorClosed
doorProg = do RingBell -- you can use (>>) because the resultant value is a Unit
              RingBell
              OpenDoor
            --   OpenDoor -- error
              Close
