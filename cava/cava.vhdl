package cava is

  component inv is
    port(signal i : in bit;
         signal o : out bit);
  end component inv;

  component and2 is
    port(signal i0, i1 : in bit;
         signal o : out bit);
   end component and2;

   component or2 is
     port(signal i0, i1 : in bit;
             signal o : out bit);
   end component or2;

end package cava;

entity inv is
  port(signal i : in bit;
       signal o : out bit);
end entity inv;

architecture cava of inv is
begin
  o <= not i;
end architecture cava;

entity and2 is
  port(signal i0, i1 : in bit;
        signal o : out bit);
end entity and2;

architecture cava of and2 is
begin
  o <=  i0 and i1;
end architecture cava;

entity or2 is
  port(signal i0, i1 : in bit;
        signal o : out bit);
end entity or2;

architecture cava of or2 is
begin
  o <=  i0 or i1;
end architecture cava;