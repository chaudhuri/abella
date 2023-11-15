open OUnit

let assert_equal_str a b =
  OUnit.assert_equal ~printer:(fun x -> x) a b

let to_string_tests =
  "To-String" >::: [
    "to_string_local_identity" >:: begin fun () ->
      let src = Source2.Local { path = "/foo/bar/baz" } in
      let str = "/foo/bar/baz" in
      assert_equal_str str Source2.(to_string src)
    end ;
    "to_string_http_empty_path" >:: begin fun () ->
      let src = Source2.(Http { host = "example.com:8080" ;
                                path = "" ;
                                secure = false }) in
      let str = "http://example.com:8080/" in
      assert_equal_str str Source2.(to_string src)
    end ;
    "to_string_http_path" >:: begin fun () ->
      let src = Source2.(Http { host = "example.com:8080" ;
                                path = "a/b" ;
                                secure = false }) in
      let str = "http://example.com:8080/a/b" in
      assert_equal_str str Source2.(to_string src)
    end ;
    "to_string_ipfs_empty_path" >:: begin fun () ->
      let src = Source2.(Ipfs { path = "" ;
                                cid = "abcd" }) in
      let str = "ipfs://abcd/" in
      assert_equal_str str Source2.(to_string src)
    end ;
    "to_string_ipfs_path" >:: begin fun () ->
      let src = Source2.(Ipfs { path = "a/b" ;
                                cid = "abcd" }) in
      let str = "ipfs://abcd/a/b" in
      assert_equal_str str Source2.(to_string src)
    end ;
  ]

let of_string_tests =
  let aeq exp got =
    OUnit.assert_equal exp got
      ~printer:Source2.to_string
  in
  "Of-String" >::: [
    "of_string_local" >:: begin fun () ->
      let exp = Source2.Local { path = "/foo/bar/baz" } in
      let got = Source2.of_string "/foo/bar/baz" in
      aeq exp got
    end ;
    "of_string_http" >:: begin fun () ->
      let exp = Source2.Http { secure = false ;
                               host = "example.com:8080" ;
                               path = "foo/bar" } in
      let got = Source2.of_string "http://example.com:8080/foo/bar" in
      aeq exp got
    end ;
    "of_string_https" >:: begin fun () ->
      let exp = Source2.Http { secure = true ;
                               host = "example.com:8080" ;
                               path = "foo/bar" } in
      let got = Source2.of_string "https://example.com:8080/foo/bar" in
      aeq exp got
    end ;
  ]

let tests =
  "Source" >::: [
    to_string_tests ;
    of_string_tests ;
  ]
