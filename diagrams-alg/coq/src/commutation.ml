
module UF = UnionFind
let (let*) = Proofview.tclBIND
let ret = Proofview.tclUNIT
let (<$>) = fun f x -> Proofview.tclBIND x (fun x -> ret (f x))
let (>>=) = Proofview.tclBIND



(*  _   _             _         *)
(* | | | | ___   ___ | | _____  *)
(* | |_| |/ _ \ / _ \| |/ / __| *)
(* |  _  | (_) | (_) |   <\__ \ *)
(* |_| |_|\___/ \___/|_|\_\___/ *)

type face =
  { side1 : UF.path
  ; side2 : UF.path
  ; eq    : Hyps.eq
  }
type hook = face -> face option Proofview.tactic

(* Precompose hook *)
let precompose_hook : Hyps.morphism -> hook = fun mph fce ->
  if fce.eq.tp.src.id = mph.data.tp.dst.id
  then
    let* r = Hyps.refl mph.data in
    let* eq = Hyps.composeP r fce.eq in
    ret (Some { side1 = (mph.data.tp.src, mph :: snd fce.side1)
              ; side2 = (mph.data.tp.src, mph :: snd fce.side2)
              ; eq    = eq
              })
  else ret None

(* Postcompose hook *)
let rec push_equality : Hyps.morphism list -> Hyps.morphism -> Hyps.eq Proofview.tactic = fun ms m ->
  match ms with
  | [ ] -> Hyps.refl m.data
  | [ m1 ] -> Hyps.compose m1.data m.data >>= Hyps.refl
  | m1 :: ms ->
    let* r = Hyps.refl m1.data in
    let* pe = push_equality ms m in
    let* pe = Hyps.composeP r pe in
    let* ms = Hyps.realize m1.data.tp.dst (Hyps.extract ms) in
    let* p  = Hyps.assoc m1.data ms m.data in
    Hyps.concat p pe

let postcompose_hook : Hyps.morphism -> hook = fun mph fce ->
  if fce.eq.tp.dst.id = mph.data.tp.src.id
  then
    let* r = Hyps.refl mph.data in
    let* eq = Hyps.composeP fce.eq r in
    let* rnorm_l = push_equality (snd fce.side1) mph in
    let* rnorm_l = Hyps.inv rnorm_l in
    let* rnorm_r = push_equality (snd fce.side2) mph in
    let* eq = Hyps.concat rnorm_l eq in
    let* eq = Hyps.concat eq rnorm_r in
    ret (Some { side1 = (fst fce.side1, List.append (snd fce.side1) [ mph ])
              ; side2 = (fst fce.side2, List.append (snd fce.side2) [ mph ])
              ; eq    = eq
              })
  else ret None

(* Monomorphism hook *)
(* If the last element matches the predicate, return the list without it *)
let rec lastrmP : ('a -> bool) -> 'a list -> 'a list option = fun pred -> function
  | [] -> None
  | [ x ] -> if pred x then Some [] else None
  | x :: l -> match lastrmP pred l with
    | Some l -> Some (x :: l)
    | None -> None

let monomorphism_hook : Hyps.morphism -> hook = fun mono fce ->
  match mono.mono with
  | None -> ret None
  | Some h when fce.eq.tp.dst.id = mono.data.tp.dst.id
             && (fst fce.side1).id = (fst fce.side2).id ->
    let pred = fun (m : Hyps.morphism) -> m.id = mono.id in
    begin match lastrmP pred (snd fce.side1), lastrmP pred (snd fce.side2) with
      | Some pth1, Some pth2 ->
        let src = fst fce.side1 in
        let* m1 = Hyps.realize src (Hyps.extract pth1) in
        let* m2 = Hyps.realize src (Hyps.extract pth2) in
        let eq  = Hyps.mono_eq h m1 m2 fce.eq in
        ret (Some { side1 = (fst fce.side1, pth1)
                  ; side2 = (fst fce.side2, pth2)
                  ; eq    =
                      { eq = eq
                      ; src = m1
                      ; dst = m2
                      ; tp = m1.tp
                      }
                  })
      | _, _ -> ret None
    end
  | _ -> ret None

(* Epimorphism hook *)
let rec path_dst_id : Hyps.elem * (Hyps.morphism list) -> Hyps.elem = fun (x,l) ->
  match l with
  | [] -> x
  | [ x ] -> x.data.tp.dst
  | _ :: xs -> path_dst_id (x,xs)

let epimorphism_hook : Hyps.morphism -> hook = fun epi fce ->
  match epi.epi with
  | None -> ret None
  | Some h when fce.eq.tp.src.id = epi.data.tp.src.id
             && path_dst_id fce.side1 = path_dst_id fce.side2 ->
    begin match snd fce.side1, snd fce.side2 with
      | epi1 :: pth1, epi2 :: pth2 when epi1.id = epi.id && epi2.id = epi.id ->
        let src = epi.data.tp.dst in
        let* m1 = Hyps.realize src (Hyps.extract pth1) in
        let* m2 = Hyps.realize src (Hyps.extract pth2) in
        let eq = Hyps.epi_eq h m1 m2 fce.eq in
        ret (Some { side1 = (src, pth1)
                  ; side2 = (src, pth2)
                  ; eq    =
                      { eq = eq
                      ; src = m1
                      ; dst = m2
                      ; tp = m1.tp
                      }
                  })
      | _, _ -> ret None
    end
  | _ -> ret None

(*   ____                                _        _   _              *)
(*  / ___|___  _ __ ___  _ __ ___  _   _| |_ __ _| |_(_) ___  _ __   *)
(* | |   / _ \| '_ ` _ \| '_ ` _ \| | | | __/ _` | __| |/ _ \| '_ \  *)
(* | |__| (_) | | | | | | | | | | | |_| | || (_| | |_| | (_) | | | | *)
(*  \____\___/|_| |_| |_|_| |_| |_|\__,_|\__\__,_|\__|_|\___/|_| |_| *)

type t =
  { union : UF.t
  ; paths : Hyps.path list
  ; hyps  : Hyps.t
  }

type buildData =
  { union : UF.t
  ; hooks : hook list
  ; level : int
  }

let query = fun p1 p2 (store : t) ->
  let* r = UF.query_conn (UF.extract p1) (UF.extract p2) store.union in
  match r with
  | None -> ret None
  | Some eq ->
    let* p = Hyps.concat p1.eq eq in
    let* p2 = Hyps.inv p2.eq in
    let* p = Hyps.concat p p2 in
    ret (Some p)

let precomposePath : Hyps.morphism -> Hyps.path -> Hyps.path Proofview.tactic = fun mph path ->
  let* c  = Hyps.compose mph.data path.mph in
  let* r  = Hyps.refl mph.data in
  let* eq = Hyps.composeP r path.eq in
  ret { Hyps.mph = c; eq = eq; path = mph :: path.path }

let forM : 'a array -> ('a -> unit Proofview.tactic) -> unit Proofview.tactic = fun arr body ->
  Array.fold_left (fun m x -> Proofview.tclTHEN m (body x)) (Proofview.tclUNIT ()) arr
let forM' : 'a list -> ('a -> unit Proofview.tactic) -> unit Proofview.tactic = fun lst body ->
  List.fold_left (fun m x -> Proofview.tclTHEN m (body x)) (Proofview.tclUNIT ()) lst

(* All paths, sorted by the index of their starting element *)
type pathEnumeration = Hyps.path list array
let singlePath : Hyps.morphism -> Hyps.path Proofview.tactic = fun m ->
  let* r = Hyps.refl m.data in
  ret { Hyps.mph = m.data
      ; eq       = r
      ; path     = [ m ]
      }
let rec enumerateAllPaths : Hyps.t -> int -> pathEnumeration Proofview.tactic = fun store level ->
  if level <= 1 then begin
    let res = Array.make (Array.length store.elems) [] in
    Proofview.tclTHEN
      (forM store.morphisms begin fun mph ->
          let* p = singlePath mph in
          res.(mph.data.tp.src.id) <- p :: res.(mph.data.tp.src.id);
          ret ()
        end)
      (ret res)
  end else begin
    let* sub = enumerateAllPaths store (level - 1) in
    let res = Array.init (Array.length sub) (fun i -> sub.(i)) in
    Proofview.tclTHEN
      (forM store.morphisms begin fun mph ->
          forM' sub.(mph.data.tp.dst.id) begin fun pth ->
            let* pth = precomposePath mph pth in
            res.(mph.data.tp.src.id) <- pth :: res.(mph.data.tp.src.id);
            ret ()
          end
        end)
      (ret res)
  end
let mergePaths : pathEnumeration -> Hyps.path list = fun enum ->
  Array.fold_right (fun lst paths -> List.append lst paths) enum []

let rec processHooks : buildData -> face -> unit Proofview.tactic = fun data face ->
  forM' data.hooks begin fun hook ->
    let* res = hook face in
    match res with
    | None -> ret ()
    | Some fce -> if List.length (snd face.side1) > data.level
                  || List.length (snd face.side2) > data.level
      then ret ()
      else addFace data fce
  end
and addFace : buildData -> face -> unit Proofview.tactic = fun data face ->
  let* added = UF.connect face.side1 face.side2 face.eq data.union in
  if added then processHooks data face else ret ()

let addEq : buildData -> Hyps.face -> unit Proofview.tactic = fun data face ->
  let* p1 = Hyps.inv face.side1.eq in
  let* p  = Hyps.concat p1 face.obj in
  let* p  = Hyps.concat p  face.side2.eq in
  addFace data
    { side1 = UF.extract face.side1; side2 = UF.extract face.side2; eq = p }

let build = fun hyps level ->
  let* paths = mergePaths <$> enumerateAllPaths hyps level in
  let* union = UF.init (List.map UF.extract paths) in
  let hooks = List.concat
    [ List.map precompose_hook   (Array.to_list hyps.morphisms)
    ; List.map postcompose_hook  (Array.to_list hyps.morphisms)
    ; List.map monomorphism_hook (Array.to_list hyps.morphisms)
    ; List.map epimorphism_hook  (Array.to_list hyps.morphisms)
    ] in
  let data = { union = union; hooks = hooks; level = level } in
  Proofview.tclTHEN
    (forM hyps.faces (addEq data))
    (ret { union = union
         ; paths = paths
         ; hyps  = hyps
         })
