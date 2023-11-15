open OUnit

let string_tests =
  let assert_equal_str a b = OUnit.assert_equal ~printer:(fun x -> x) a b in
  "String" >::: [
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
  ]

let tests =
  "Source" >::: [
    string_tests ;
  ]
