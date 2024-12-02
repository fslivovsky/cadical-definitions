#include "interrupt.hpp"

namespace definability_interpolation {

int interrupt_handler::signal_received = 0;

void interrupt_handler::interrupt(int signal) {
  signal_received = signal;
}

int interrupt_handler::interrupted(void*) {
  return signal_received;
}

const char* interrupted_exception::what() {
  return "SAT call interrupted";
}

}