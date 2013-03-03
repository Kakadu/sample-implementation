{{{{skip;
    read (n)};
   skip};
  {{{r := 1 * n;
     n := n * n};
    skip};
   {{{r := r * n;
      n := n * n};
     skip};
    {{{skip;
       n := n * n};
      skip};
     {{{r := r * n;
        n := n * n};
       skip};
      skip}}}}};
 write (r)}
