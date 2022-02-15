open_vcd aes_sub_bytes_tb.vcd
log_vcd *
log_vcd [ get_objects * ]
add_force {/aes_sub_bytes_tb/clk} {0 0ns} {1 50ns} -repeat_every 100ns
run 2900ns
flush_vcd
close_vcd
exit
