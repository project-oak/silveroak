open_vcd aes_mix_columns_tb.vcd
log_vcd *
log_vcd [ get_objects * ]
add_force {/aes_mix_columns_tb/clk} {0 0ns} {1 50ns} -repeat_every 100ns
run 2700ns
flush_vcd
close_vcd
exit
