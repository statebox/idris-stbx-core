#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

int readInt() {
  char buffer[1];

  printf("Please enter an integer value\n");

  read(STDIN_FILENO, buffer, 1);

  return buffer[0];
}

int generateInt() {
  int chaos;

  srand(time(NULL));

  chaos = rand() % 100000;

  printf("The generated number is %d\n", chaos);

  return chaos;
}