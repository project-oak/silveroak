open_vcd aes_add_round_key_tb.vcd
log_vcd *
log_vcd [ get_objects * ]
add_force {/aes_add_round_key_tb/clk} {0 0ns} {1 50ns} -repeat_every 100ns
run 3100ns
flush_vcd
close_vcd
exit
