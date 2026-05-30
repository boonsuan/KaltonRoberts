.PHONY: verify

verify:
	lake build
	python3 scripts/check_active_sorries.py
	python3 scripts/verify_halving.py
