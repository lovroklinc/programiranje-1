type vector = { x : float; y : float }

let ( **. ) k vec = { x = k *. vec.x; y = k *. vec.y }
let ( ++. ) vec1 vec2 = { x = vec1.x +. vec2.x; y = vec1.y +. vec2.y }
let ( --. ) vec1 vec2 = vec1 ++. (-1. **. vec2)
let length vec = sqrt ((vec.x ** 2.) +. (vec.y ** 2.))
let normalize vec = (1. /. length vec) **. vec

let midpoint ?(lambda = 0.5) source target =
  ((1. -. lambda) **. source) ++. (lambda **. target)

let distance source target = length (source --. target)

type state = { name : string }

type fsm = {
  states : state list;
  initial : state;
  final : state list;
  transitions : (state * char * state) list;
}

let step fsm chr state =
  let rec find_transition = function
    | [] -> None
    | (src, char, dst) :: _ when src = state && char = chr -> Some dst
    | _ :: rest -> find_transition rest
  in
  find_transition fsm.transitions

type mode = Normal | Dragging of state

type model = {
  fsm : fsm;
  positions : (state * vector) list;
  mode : mode;
  width : float;
  height : float;
  characters : char list;
  current_state : state;
}

type msg = DragStart of state | DragMove of vector | DragEnd | Next

let state_position model state = List.assoc state model.positions

let update model = function
  | DragStart state -> { model with mode = Dragging state }
  | DragMove position -> (
      match model.mode with
      | Dragging state ->
          let positions =
            List.map
              (fun (state', position') ->
                (state', if state = state' then position else position'))
              model.positions
          in
          { model with positions }
      | Normal -> model)
  | DragEnd -> { model with mode = Normal }
  | Next -> (
      match model.characters with
      | chr :: characters -> (
          match step model.fsm chr model.current_state with
          | None -> model
          | Some state' -> { model with current_state = state'; characters })
      | [] -> model)
