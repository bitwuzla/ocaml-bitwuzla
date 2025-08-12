(**************************************************************************)
(*  Bitwuzla: Satisfiability Modulo Theories (SMT) solver.                *)
(*                                                                        *)
(*  Copyright (C) 2023 by the authors listed in the AUTHORS file at       *)
(*  https://github.com/bitwuzla/bitwuzla/blob/main/AUTHORS                *)
(*                                                                        *)
(*  This file is part of Bitwuzla under the MIT license.                  *)
(*  See COPYING for more information at                                   *)
(*  https://github.com/bitwuzla/bitwuzla/blob/main/COPYING                *)
(**************************************************************************)
let n = Array.length Examples.collection

let run i () =
  let module M = Bitwuzla_cxx.Make () in
  try
    Array.for_all
      (fun f -> f (module M : Bitwuzla_cxx.S) (Bitwuzla_cxx.Options.default ()))
      (Array.init n (fun j -> Array.get Examples.collection ((i + j) mod n)))
  with _ -> false

let%test "domains" =
  Array.for_all Fun.id
    (Array.map Domain.join
       (Array.init (Domain.recommended_domain_count ()) (fun i ->
            Domain.spawn (run i))))

let%test "issues/7" =
  let run () =
    let module M = Bitwuzla_cxx.Make () in
    let _ = M.mk_bool_sort () in
    true
  in
  Array.for_all Fun.id
    (Array.map Domain.join
       (Array.init (Domain.recommended_domain_count ()) (fun _ ->
            Domain.spawn run)))
