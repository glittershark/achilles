default: simple

%.ll: %.ach
	cargo run -- compile $< -o $@ -f llvm

%.o: %.ll
	llc $< -o $@ -filetype=obj

%: %.o
	clang $< -o $@

.PHONY: clean

clean:
	@rm -f *.ll *.o simple functions
