"use strict";

exports.toneDeafJsDoIt = function (n) {
  console.log('now in toneDeafJsDoIt2');
  return "hello tone deaf";
};

exports.createVtEvt = function (n) {
  // return new CustomEvent('vtEvt');
  var evt = document.createEvent('Event');
  evt.initEvent('vtEvt', true, true)

  return evt;
}

// exports.debugIt = function () {
//   // debugger;
//   return "hi from debugIt";
// }
// exports.debugIt = function (n) {
exports.toneDeafAbc = function (n) {
  console.log('now in debugIt');
  debugger;
  return "debug tone deaf";
};

exports.toneDeafEvt = function (evt) {
  console.log('now in tonDeafEvt');
  debugger;
  return "debug tone deaf";
};
