#ifndef CADICAL_INTERRUPT_H_
#define CADICAL_INTERRUPT_H_

#include <iostream>
#include <exception>

namespace definability_interpolation {

class interrupted_exception: std::exception {
  virtual const char* what();
};

class interrupt_handler {
 public:
  static void interrupt(int signal);
  static int interrupted(void*);

 private:
  static int signal_received;
};

}

#endif // CADICAL_INTERRUPT_H_