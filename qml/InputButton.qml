import QtQuick 2.0
import QtQuick.Controls 1.4

Button {
  property string textDisplayed
  property string textInserted
  text: textDisplayed
  onClicked: function() {
    // TODO: respektuj pozycje kursora
    input.text += textInserted
  }
}
