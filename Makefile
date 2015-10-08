test: test.mlb test.sml unsynchronized.sml test_main.sml
	mlton -codegen amd64 test.mlb
