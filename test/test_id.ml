open Test_helper
open Abella_lib

let a = Id.intern "a"
let b = Id.intern "b"

let ids ss = List.map Id.intern ss

let check_bindings msg expected t =
  Alcotest.check (Alcotest.list (Alcotest.pair id_testable Alcotest.int))
    msg expected (Id.Map.bindings t)

let tests =
  suite "Id" [
      test_case "Interning is consistent"
        (fun () ->
           Alcotest.check Alcotest.bool "equal ids" true
             (Id.equal (Id.intern "x") (Id.intern "x")) ;
           Alcotest.check Alcotest.bool "unequal ids" false
             (Id.equal (Id.intern "x") (Id.intern "y")) ;
           Alcotest.check Alcotest.string "value roundtrip" "x"
             (Id.value (Id.intern "x")) ;
           ()) ;

      test_case "Id.Map small map operations"
        (fun () ->
           let t = Id.Map.(empty |> add b 2 |> add a 1) in
           Alcotest.check Alcotest.int "cardinal" 2 (Id.Map.cardinal t) ;
           Alcotest.check Alcotest.bool "mem" true (Id.Map.mem a t) ;
           Alcotest.check Alcotest.bool "not mem" false
             (Id.Map.mem (Id.intern "z") t) ;
           Alcotest.check Alcotest.int "find" 1 (Id.Map.find a t) ;
           Alcotest.check (Alcotest.option Alcotest.int) "find_opt" (Some 2)
             (Id.Map.find_opt b t) ;
           Alcotest.check (Alcotest.option Alcotest.int) "find_opt missing"
             None (Id.Map.find_opt (Id.intern "z") t) ;
           Alcotest.check_raises "find missing" Not_found
             (fun () -> ignore (Id.Map.find (Id.intern "z") t)) ;
           let t = Id.Map.remove a t in
           Alcotest.check Alcotest.bool "removed" false (Id.Map.mem a t) ;
           Alcotest.check Alcotest.int "find remaining" 2
             (Id.Map.find b t)) ;

      test_case "Id.Map bindings are sorted by name"
        (fun () ->
           let t =
             List.fold_left (fun t (s, v) -> Id.Map.add (Id.intern s) v t)
               Id.Map.empty
               ["d", 4 ; "b", 2 ; "a", 1 ; "c", 3]
           in
           check_bindings "sorted bindings"
             (List.map (fun (s, v) -> (Id.intern s, v))
                ["a", 1 ; "b", 2 ; "c", 3 ; "d", 4])
             t ;
           let folded = Id.Map.fold (fun id v acc -> (id, v) :: acc)
               t [] |> List.rev in
           Alcotest.check (Alcotest.list (Alcotest.pair id_testable Alcotest.int))
             "fold order" (Id.Map.bindings t) folded) ;

      test_case "Id.Map grows past the small representation"
        (fun () ->
           let entries =
             List.init 20 (fun i -> ("k" ^ string_of_int i, i))
           in
           let t =
             List.fold_left
               (fun t (s, v) -> Id.Map.add (Id.intern s) v t)
               Id.Map.empty entries
           in
           Alcotest.check Alcotest.int "cardinal" 20 (Id.Map.cardinal t) ;
           List.iter begin fun (s, v) ->
             Alcotest.check Alcotest.int ("find " ^ s) v
               (Id.Map.find (Id.intern s) t)
           end entries ;
           let names =
             List.map (fun (id, _) -> Id.value id) (Id.Map.bindings t)
           in
           Alcotest.check (Alcotest.list Alcotest.string) "sorted names"
             (List.sort String.compare (List.map fst entries)) names ;
           let t = Id.Map.remove (Id.intern "k7") t in
           Alcotest.check Alcotest.int "cardinal after remove" 19
             (Id.Map.cardinal t) ;
           Alcotest.check (Alcotest.option Alcotest.int) "removed" None
             (Id.Map.find_opt (Id.intern "k7") t)) ;

      test_case "Id.Map duplicate add keeps size"
        (fun () ->
           let t = Id.Map.(add a 1 (add a 0 empty)) in
           Alcotest.check Alcotest.int "cardinal" 1 (Id.Map.cardinal t) ;
           Alcotest.check Alcotest.int "latest wins" 1 (Id.Map.find a t)) ;

      test_case "Id.Set operations"
        (fun () ->
           let s = Id.Set.of_list (ids ["b"; "a"; "b"]) in
           Alcotest.check Alcotest.int "cardinal" 2 (Id.Set.cardinal s) ;
           Alcotest.check Alcotest.bool "mem" true (Id.Set.mem a s) ;
           Alcotest.check (Alcotest.list id_testable) "elements sorted"
             (ids ["a"; "b"]) (Id.Set.elements s) ;
           let s = Id.Set.remove a s in
           Alcotest.check Alcotest.bool "removed" false (Id.Set.mem a s) ;
           Alcotest.check Alcotest.bool "equal" true
             (Id.Set.equal s (Id.Set.singleton b)) ;
           Alcotest.check Alcotest.bool "not equal" false
             (Id.Set.equal s (Id.Set.of_list (ids ["a"; "b"])))) ;

      test_case "Id.Set grows past the small representation"
        (fun () ->
           let names = List.init 20 (fun i -> "m" ^ string_of_int i) in
           let s = Id.Set.of_list (ids names) in
           Alcotest.check Alcotest.int "cardinal" 20 (Id.Set.cardinal s) ;
           Alcotest.check (Alcotest.list id_testable) "elements sorted"
             (ids (List.sort String.compare names)) (Id.Set.elements s) ;
           Alcotest.check Alcotest.bool "equal large" true
             (Id.Set.equal s (Id.Set.of_list (ids (List.rev names)))) ;
           let s = Id.Set.remove (Id.intern "m3") s in
           Alcotest.check Alcotest.bool "removed" false
             (Id.Set.mem (Id.intern "m3") s)) ;
    ]
