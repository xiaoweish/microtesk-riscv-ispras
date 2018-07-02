#!/bin/bash
rm $MICROTESK_HOME/$1*.s \
   $MICROTESK_HOME/$1*.ld \
   $MICROTESK_HOME/$1*.dump \
   $MICROTESK_HOME/$1*.o \
   $MICROTESK_HOME/$1*.bin \
   $MICROTESK_HOME/$1*.elf \
   $MICROTESK_HOME/$1*.stdout \
   $MICROTESK_HOME/$1*.stderr -f
