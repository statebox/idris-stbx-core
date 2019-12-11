#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>

int readInt(char *whatToEnter) {
  char buffer[2];

  printf("C: Please enter an integer value for the %s\n", whatToEnter);

  read(STDIN_FILENO, buffer, 2);

  printf("C: The number %d was given\n", buffer[0] - 48);

  return (int) buffer[0];
}

int generateInt() {
  int chaos;

  srand(time(NULL));

  chaos = rand() % 100000;

  printf("C: The generated number is %d\n", chaos);

  return chaos;
}